import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const buildDir = path.resolve(process.argv[2] || path.join(scriptDir, 'build'));
const { default: createTinyshogi } = await import(
  pathToFileURL(path.join(buildDir, 'tinyshogi.js')));

const module = await createTinyshogi({
  wasmBinary: fs.readFileSync(path.join(buildDir, 'tinyshogi.wasm'))
});
const cwrap = (name, returnType, argumentTypes) =>
  module.cwrap(name, returnType, argumentTypes);
const init = cwrap('web_init', null, []);
const reset = cwrap('web_reset', null, []);
const getSfen = cwrap('web_get_sfen', 'string', []);
const legalMoveCount = cwrap('web_legal_move_count', 'number', []);
const playMove = cwrap('web_play_move', 'number', ['number']);
const undo = cwrap('web_undo', 'number', []);
const redo = cwrap('web_redo', 'number', []);
const engineMove = cwrap('web_engine_move', 'string', ['number']);
const gameResult = cwrap('web_game_result', 'number', []);
const memoryBytes = cwrap('web_memory_bytes', 'number', []);

const games = 1;
const nodes = 4096;
let totalPlies = 0;
let peakMemory = 0;

init();
peakMemory = memoryBytes();
const startSfen = getSfen();
assert.equal(legalMoveCount(), 30);
assert.equal(legalMoveCount(), 30, 'cached legal move count changed');
assert.equal(playMove(0), 1);
assert.notEqual(getSfen(), startSfen);
assert.equal(undo(), 1);
assert.equal(getSfen(), startSfen);
assert.equal(legalMoveCount(), 30, 'undo did not invalidate the legal-move cache');
assert.equal(redo(), 1);
assert.notEqual(getSfen(), startSfen);
reset();
for (let game = 0; game < games; ++game) {
  reset();
  let plies = 0;
  while (gameResult() === 0 && plies < 512) {
    assert.notEqual(engineMove(nodes), '', `empty move in game ${game + 1}, ply ${plies}`);
    peakMemory = Math.max(peakMemory, memoryBytes());
    ++plies;
  }
  assert.notEqual(gameResult(), 0, `game ${game + 1} did not finish`);
  totalPlies += plies;
}

reset();
assert.notEqual(engineMove(2000000), '', 'maximum-budget search returned no move');
peakMemory = Math.max(peakMemory, memoryBytes());
assert.ok(peakMemory <= 640 * 1024,
  `WASM linear memory grew beyond the low-memory budget: ${peakMemory} bytes`);
console.log(`PASS WASM engine self-play: ${games} games, ${totalPlies} plies, ${nodes} nodes plus maximum-budget stress, ${Math.round(peakMemory / 1024)} KiB peak linear memory`);
