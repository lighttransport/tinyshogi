import createTinyshogi from './build/tinyshogi.js';

createTinyshogi().then(module => {
const api = {
  init: module.cwrap('web_init', null, []),
  setSfen: module.cwrap('web_set_sfen', 'number', ['string']),
  engineMove: module.cwrap('web_engine_move', 'string', ['number']),
  getSfen: module.cwrap('web_get_sfen', 'string', [])
};
api.init();

self.onmessage = event => {
  const { sfen, nodes = 64 } = event.data || {};
  if (!api.setSfen(sfen || '')) {
    self.postMessage({ error: 'Invalid SFEN' });
    return;
  }
  const move = api.engineMove(nodes);
  self.postMessage({ move, sfen: api.getSfen() });
};
});
