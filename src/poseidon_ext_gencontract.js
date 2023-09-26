// Copyright (c) 2018 Jordi Baylina
// License: LGPL-3.0+
//

const Contract = require("./evmasm");
const { unstringifyBigInts } = require("ffjavascript").utils;
const Web3Utils = require("web3-utils");

const { C:K, M } = unstringifyBigInts(require("./poseidon_constants.json"));

const N_ROUNDS_F = 8;
const N_ROUNDS_P = [56, 57, 56, 60, 60, 63, 64, 63];

function toHex256(a) {
    let S = a.toString(16);
    while (S.length < 64) S="0"+S;
    return "0x" + S;
}

// generates the code for the poseidon hash function that lets you set the 0th element of
// the initial sponge state. this is identical to the `PoseidonExt` template from `circomlib`.
// specifically, the signature is:
// poseidonExt(uint256 initialState,uint256[nInputs] inputs), where
//  - `initialState` is the 0th element of the initial sponge state
//  - `inputs` is a static array of inputs to hash
//
// note that neither `inputs` nor `initialStates` are checked to be valid fieild elements
function createCode(nInputs) {

    if (( nInputs<1) || (nInputs>8)) throw new Error("Invalid number of inputs. Must be 1<=nInputs<=8");
    const t = nInputs + 1;
    const nRoundsF = N_ROUNDS_F;
    const nRoundsP = N_ROUNDS_P[t - 2];

    const C = new Contract();

    function saveM() {
        for (let i=0; i<t; i++) {
            for (let j=0; j<t; j++) {
                C.push(toHex256(M[t-2][i][j]));
                C.push((1+i*t+j)*32);
                C.mstore();
            }
        }
    }

    function ark(r) {   // st, q
        for (let i=0; i<t; i++) {
            C.dup(t); // q, st, q
            C.push(toHex256(K[t-2][r*t+i]));  // K, q, st, q
            C.dup(2+i); // st[i], K, q, st, q
            C.addmod(); // newSt[i], st, q
            C.swap(1 + i); // xx, st, q
            C.pop();
        }
    }

    function sigma(p) {
        // sq, q
        C.dup(t);   // q, st, q
        C.dup(1+p); // st[p] , q , st, q
        C.dup(1);   // q, st[p] , q , st, q
        C.dup(0);   // q, q, st[p] , q , st, q
        C.dup(2);   // st[p] , q, q, st[p] , q , st, q
        C.dup(0);   // st[p] , st[p] , q, q, st[p] , q , st, q
        C.mulmod(); // st2[p], q, st[p] , q , st, q
        C.dup(0);   // st2[p], st2[p], q, st[p] , q , st, q
        C.mulmod(); // st4[p], st[p] , q , st, q
        C.mulmod(); // st5[p], st, q
        C.swap(1+p);
        C.pop();      // newst, q
    }

    function mix() {
        C.label("mix");
        for (let i=0; i<t; i++) {
            for (let j=0; j<t; j++) {
                if (j==0) {
                    C.dup(i+t);      // q, newSt, oldSt, q
                    C.push((1+i*t+j)*32);
                    C.mload();      // M, q, newSt, oldSt, q
                    C.dup(2+i+j);    // oldSt[j], M, q, newSt, oldSt, q
                    C.mulmod();      // acc, newSt, oldSt, q
                } else {
                    C.dup(1+i+t);    // q, acc, newSt, oldSt, q
                    C.push((1+i*t+j)*32);
                    C.mload();      // M, q, acc, newSt, oldSt, q
                    C.dup(3+i+j);    // oldSt[j], M, q, acc, newSt, oldSt, q
                    C.mulmod();      // aux, acc, newSt, oldSt, q
                    C.dup(2+i+t);    // q, aux, acc, newSt, oldSt, q
                    C.swap(2);       // acc, aux, q, newSt, oldSt, q
                    C.addmod();      // acc, newSt, oldSt, q
                }
            }
        }
        for (let i=0; i<t; i++) {
            C.swap((t -i) + (t -i-1));
            C.pop();
        }
        C.push(0);
        C.mload();
        C.jmp();
    }


    // Check selector
    // load the first 32-byte word onto the stack and divide by `0x0100000000000000000000000000000000000000000000000000000000`
    // to clear the upper 28 bytes, leaving the 4-byte selector
    // then we compare with the selector for poseidon(uint256,uint256[n])
    // if the selector matches, then we jump to `start` label (`C.label("start")` below)
    // otherwise we revert
    C.push("0x0100000000000000000000000000000000000000000000000000000000");
    C.push(0);
    C.calldataload();
    C.div();
    C.dup(0);
    C.push(Web3Utils.keccak256(`poseidonExt(uint256,uint256[${nInputs}])`).slice(0, 10)); // poseidon(uint256,uint256[n])
    C.eq();
    C.swap(1);
    C.push(Web3Utils.keccak256(`poseidonExt(uint256,bytes32[${nInputs}])`).slice(0, 10)); // poseidon(uint256,bytes32[n])
    C.eq();
    C.or();
    C.jmpi("start");
    C.invalid();

    C.label("start");

    // push the MDS matrix onto the stack
    // -> [MDS] 
    saveM();

    // push `q`, the BN254 scalar field modulus, onto the stack
    // [q (32B)] [MDS (big, don't really care)]
    C.push("0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"); 

    // load initial state
    // to do this, we load nInputs = t-1 inputs from calldata onto the stack, forming the 1st through tth elements of the sponge state
    // and then load the initial state from calldata onto the stack as the 0th element of the sponge state
    //
    // The function has two params: an initial state followed by a static array param,
    // so calldata will look like:
    // [selector (4B)] [initialState (32B)] [inputs[0] (32B)] [inputs[1] (32B)] ... [inputs[t-1] (32B)]
    //
    // afterwards, we want to end up with:
    // [initialState] [inputs[0] (32B)] [inputs[1] (32B)] ... [inputs[t-1] (32B)] [q (32B)] [MDS]
    //
    // contrast to `poseidon` from `posedion_gencontract.js` which initializes the 0th element of the sponge state to 0,
    // which results in a stack like this:
    // [0 (32B)] [inputs[0] (32B)] [inputs[1] (32B)] ... [inputs[t-1] (32B)] [q (32B)] [MDS]

    // load inputs onto stack in reverse order so they are in the correct order for consumer
    // -> [inputs[0]] [inputs[1]] ... [inputs[t-1]] [initialState] [q] [MDS]
    for (let i=0; i<nInputs; i++) {
        C.push(0x04 + 0x20 + (0x20 * (nInputs - i - 1)));
        C.calldataload();
    }

    // load initial state onto stack atop the inputs
    // -> [initialState] [inputs[0]] [inputs[1]] ... [inputs[t-1]] [q] [MDS]
    C.push(0x04);
    C.calldataload();

    // now that the state is set up on the stack,
    // rest is the same as the "normal" poseidon in `poseidon_gencontract.js`

    for (let i=0; i<nRoundsF+nRoundsP; i++) {
        ark(i);
        if ((i<nRoundsF/2) || (i>=nRoundsP+nRoundsF/2)) {
            for (let j=0; j<t; j++) {
                sigma(j);
            }
        } else {
            sigma(0);
        }
        const strLabel = "aferMix"+i;
        C._pushLabel(strLabel);
        C.push(0);
        C.mstore();
        C.jmp("mix");
        C.label(strLabel);
    }

    C.push("0x00");
    C.mstore();     // Save it to pos 0;
    C.push("0x20");
    C.push("0x00");
    C.return();

    mix();

    return C.createTxData();
}

function generateABI(nInputs) {
    return [
        {
            "constant": true,
            "inputs": [
                {
                    "internalType": `uint256`,
                    "name": "initialState",
                    "type": "uint256"
                },
                {
                    "internalType": `bytes32[${nInputs}]`,
                    "name": "input",
                    "type": `bytes32[${nInputs}]`
                }
            ],
            "name": "poseidonExt",
            "outputs": [
                {
                    "internalType": "bytes32",
                    "name": "",
                    "type": "bytes32"
                }
            ],
            "payable": false,
            "stateMutability": "pure",
            "type": "function"
        },
        {
            "constant": true,
            "inputs": [
                {
                    "internalType": `uint256`,
                    "name": "initialState",
                    "type": "uint256"
                },
                {
                    "internalType": `uint256[${nInputs}]`,
                    "name": "input",
                    "type": `uint256[${nInputs}]`
                }
            ],
            "name": "poseidonExt",
            "outputs": [
                {
                    "internalType": "uint256",
                    "name": "",
                    "type": "uint256"
                }
            ],
            "payable": false,
            "stateMutability": "pure",
            "type": "function"
        }
    ];
}

module.exports.generateABI = generateABI;
module.exports.createCode = createCode;

