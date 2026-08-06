import createTinyshogi from './build/tinyshogi.js';

async function main() {
const module = await createTinyshogi();
const api = {
  init: module.cwrap('web_init', null, []),
  reset: module.cwrap('web_reset', null, []),
  pieceAt: module.cwrap('web_piece_at', 'number', ['number']),
  side: module.cwrap('web_side_to_move', 'number', []),
  hand: module.cwrap('web_hand_count', 'number', ['number', 'number']),
  count: module.cwrap('web_legal_move_count', 'number', []),
  from: module.cwrap('web_move_from', 'number', ['number']),
  to: module.cwrap('web_move_to', 'number', ['number']),
  promotes: module.cwrap('web_move_promotes', 'number', ['number']),
  drop: module.cwrap('web_move_drop', 'number', ['number']),
  play: module.cwrap('web_play_move', 'number', ['number']),
  playUsi: module.cwrap('web_play_usi', 'number', ['string']),
  canUndo: module.cwrap('web_can_undo', 'number', []),
  canRedo: module.cwrap('web_can_redo', 'number', []),
  undo: module.cwrap('web_undo', 'number', []),
  redo: module.cwrap('web_redo', 'number', []),
  getSfen: module.cwrap('web_get_sfen', 'string', []),
  setSfen: module.cwrap('web_set_sfen', 'number', ['string']),
  result: module.cwrap('web_game_result', 'number', [])
};
const engineWorker = new Worker(new URL('./engine-worker.js', import.meta.url), { type: 'module' });
let engineBusy = false;

const board = document.querySelector('#board');
const status = document.querySelector('#status');
const sfen = document.querySelector('#sfen');
let selected = -1;
let selectedDrop = 0;

const names = ['', '歩', '香', '桂', '銀', '金', '角', '飛', '玉', 'と', '杏', '圭', '全', '馬', '龍'];
const handNames = ['歩', '香', '桂', '銀', '金', '角', '飛'];

function legalMoves() {
  const moves = [];
  for (let i = 0; i < api.count(); ++i) {
    moves.push({ index: i, from: api.from(i), to: api.to(i), promotes: api.promotes(i), drop: api.drop(i) });
  }
  return moves;
}

function render() {
  const moves = legalMoves();
  const targets = new Set(moves.filter(move => selectedDrop
    ? move.from === 255 && move.drop === selectedDrop
    : move.from === selected).map(move => move.to));
  board.replaceChildren();
  for (let square = 0; square < 81; ++square) {
    const button = document.createElement('button');
    const piece = api.pieceAt(square);
    button.className = 'square' + (piece > 0 ? ' black' : piece < 0 ? ' white' : '');
    if (square === selected) button.classList.add('selected');
    if (targets.has(square)) button.classList.add('target');
    button.textContent = piece ? names[Math.abs(piece)] : '';
    button.addEventListener('click', () => clickSquare(square, moves));
    board.append(button);
  }
  renderHands();
  const result = api.result();
  status.textContent = result === 0 ? (api.side() === 0 ? 'Black to move' : 'White to move')
    : result === 1 ? 'Black wins' : result === 2 ? 'White wins' : 'Draw';
  sfen.value = api.getSfen();
  document.querySelector('#undo').disabled = !api.canUndo();
  document.querySelector('#redo').disabled = !api.canRedo();
  document.querySelector('#engine-move').disabled = engineBusy || result !== 0;
}

function renderHands() {
  for (const color of [0, 1]) {
    const hand = document.querySelector(`#hand-${color}`);
    hand.replaceChildren();
    for (let index = 0; index < handNames.length; ++index) {
      const type = index + 1;
      const count = api.hand(color, index);
      const button = document.createElement('button');
      button.className = 'hand-piece' + (selectedDrop === type && api.side() === color ? ' selected' : '');
      button.textContent = `${handNames[index]} ${count || ''}`;
      button.disabled = color !== api.side() || count === 0;
      button.addEventListener('click', () => {
        selected = -1;
        selectedDrop = selectedDrop === type ? 0 : type;
        render();
      });
      hand.append(button);
    }
  }
}

function clickSquare(square, moves) {
  const candidates = moves.filter(candidate => candidate.to === square && (selectedDrop
    ? candidate.from === 255 && candidate.drop === selectedDrop
    : candidate.from === selected));
  if (candidates.length > 0) {
    let move = candidates[0];
    if (candidates.length > 1) {
      move = window.confirm('Promote this piece?')
        ? candidates.find(candidate => candidate.promotes)
        : candidates.find(candidate => !candidate.promotes);
    }
    if (move) api.play(move.index);
    selected = -1;
    selectedDrop = 0;
    render();
    return;
  }
  if (selectedDrop) { selectedDrop = 0; render(); return; }
  const piece = api.pieceAt(square);
  if (piece && (piece > 0) === (api.side() === 0)) selected = square;
  else selected = -1;
  render();
}

function refresh() { selected = -1; selectedDrop = 0; render(); }
document.querySelector('#reset').addEventListener('click', () => { api.reset(); refresh(); });
document.querySelector('#undo').addEventListener('click', () => { if (api.undo()) refresh(); });
document.querySelector('#redo').addEventListener('click', () => { if (api.redo()) refresh(); });
document.querySelector('#load-sfen').addEventListener('click', () => {
  if (!api.setSfen(sfen.value.trim())) window.alert('Invalid SFEN');
  refresh();
});
document.querySelector('#engine-move').addEventListener('click', () => {
  if (engineBusy) return;
  engineBusy = true;
  render();
  engineWorker.postMessage({ sfen: api.getSfen(), nodes: 64 });
});
engineWorker.onmessage = event => {
  engineBusy = false;
  if (event.data.error || !event.data.move || !api.playUsi(event.data.move)) {
    window.alert(event.data.error || 'Engine search failed');
  }
  refresh();
};
document.addEventListener('keydown', event => {
  if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 'z') {
    event.preventDefault();
    if (event.shiftKey ? api.redo() : api.undo()) refresh();
  }
});
api.init();
render();
}

main();
