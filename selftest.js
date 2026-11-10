// Extracts the Chord core from index.html and runs randomized consistency tests.
const fs = require("fs");
const path = require("path");

const html = fs.readFileSync(path.join(__dirname, "..", "index.html"), "utf8");
const core = html.split("// CORE-START")[1].split("// CORE-END")[0];
const { selfTest } = new Function(core + "; return { selfTest };")();

try {
  for (let run = 1; run <= 3; run++) {
    console.log(`--- run ${run} ---`);
    selfTest().forEach((l) => console.log(l));
  }
  console.log("All Chord tests passed.");
} catch (e) {
  console.error("TEST FAILED:", e.message);
  process.exit(1);
}
