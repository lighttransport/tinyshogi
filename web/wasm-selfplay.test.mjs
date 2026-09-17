import assert from 'node:assert/strict';
import fs from 'node:fs';
import createTinyshogi from './build/tinyshogi.js';

const module = await createTinyshogi({
  wasmBinary: fs.readFileSync(new URL('./build/tinyshogi.wasm', import.meta.url))
});
const cwrap = (name, returnType, argumentTypes) =>
  module.cwrap(name, returnType, argumentTypes);
const init = cwrap('web_init', null, []);
const reset = cwrap('web_reset', null, []);
const engineMove = cwrap('web_engine_move', 'string', ['number']);
const gameResult = cwrap('web_game_result', 'number', []);

const games = 3;
const nodes = 4096;
let totalPlies = 0;

init();
for (let game = 0; game < games; ++game) {
  reset();
  let plies = 0;
  while (gameResult() === 0 && plies < 512) {
    assert.notEqual(engineMove(nodes), '', `empty move in game ${game + 1}, ply ${plies}`);
    ++plies;
  }
  assert.notEqual(gameResult(), 0, `game ${game + 1} did not finish`);
  totalPlies += plies;
}

console.log(`PASS WASM engine self-play: ${games} games, ${totalPlies} plies, ${nodes} nodes`);
