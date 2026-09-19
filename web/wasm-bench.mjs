import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { performance } from 'node:perf_hooks';

const buildDir = process.argv[2] || 'build';
const nodeBudget = Number(process.argv[3] || 250000);
const runs = Number(process.argv[4] || 5);
if (!Number.isSafeInteger(nodeBudget) || nodeBudget < 1 ||
    !Number.isSafeInteger(runs) || runs < 1) {
  throw new Error('usage: node wasm-bench.mjs [build-dir] [nodes] [runs]');
}

const jsPath = path.resolve(buildDir, 'tinyshogi.js');
const wasmPath = path.resolve(buildDir, 'tinyshogi.wasm');
const { default: createTinyshogi } = await import(pathToFileURL(jsPath));
const module = await createTinyshogi({ wasmBinary: fs.readFileSync(wasmPath) });
const cwrap = (name, returnType, argumentTypes) =>
  module.cwrap(name, returnType, argumentTypes);
const init = cwrap('web_init', null, []);
const reset = cwrap('web_reset', null, []);
const engineMove = cwrap('web_engine_move', 'string', ['number']);
const searchedNodes = cwrap('web_engine_last_nodes', 'number', []);
const memoryBytes = cwrap('web_memory_bytes', 'number', []);

init();
const initialMemoryBytes = memoryBytes();
/* Trigger lazy JS/WASM compilation outside the measured rounds. */
engineMove(Math.min(nodeBudget, 4096));

let elapsedMs = 0;
let totalNodes = 0;
let peakMemoryBytes = Math.max(initialMemoryBytes, memoryBytes());
let lastMove = '';
for (let run = 0; run < runs; ++run) {
  reset();
  const started = performance.now();
  lastMove = engineMove(nodeBudget);
  elapsedMs += performance.now() - started;
  totalNodes += searchedNodes();
  peakMemoryBytes = Math.max(peakMemoryBytes, memoryBytes());
  if (!lastMove) throw new Error(`empty move in round ${run + 1}`);
}

console.log(JSON.stringify({
  buildDir,
  runs,
  nodeBudget,
  totalNodes,
  elapsedMs: Math.round(elapsedMs),
  nodesPerSecond: Math.round(totalNodes / (elapsedMs / 1000)),
  initialMemoryBytes,
  peakMemoryBytes,
  wasmBytes: fs.statSync(wasmPath).size,
  lastMove
}));
