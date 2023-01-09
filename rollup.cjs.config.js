import fs from "fs";
import { builtinModules as builtin } from "module";
import nodePolyfills from "rollup-plugin-polyfill-node";
import resolve from "@rollup/plugin-node-resolve";

const pkg = JSON.parse(fs.readFileSync("./package.json"));

export default {
  input: "./main.js",
  output: {
    file: "build/main.cjs",
    format: "cjs",
  },
  external: [...Object.keys(pkg.dependencies), ...builtin],
  plugins: [nodePolyfills(), resolve()],
};
