import createTinyshogi from './build/tinyshogi.js';
import { WebGpuNnue } from './nnue-webgpu.js';

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
  historyCount: module.cwrap('web_history_count', 'number', []),
  historyMove: module.cwrap('web_history_move', 'string', ['number']),
  timelineCount: module.cwrap('web_timeline_count', 'number', []),
  timelineMove: module.cwrap('web_timeline_move', 'string', ['number']),
  undo: module.cwrap('web_undo', 'number', []),
  redo: module.cwrap('web_redo', 'number', []),
  getSfen: module.cwrap('web_get_sfen', 'string', []),
  getRootSfen: module.cwrap('web_get_root_sfen', 'string', []),
  setSfen: module.cwrap('web_set_sfen', 'number', ['string']),
  result: module.cwrap('web_game_result', 'number', []),
  nnueFeatureCount: module.cwrap('web_nnue_feature_count', 'number', ['number']),
  nnueFeatureId: module.cwrap('web_nnue_feature_id', 'number', ['number', 'number']),
  nnueMoveFeatureCount: module.cwrap('web_nnue_move_feature_count', 'number', ['number', 'number']),
  nnueMoveFeatureId: module.cwrap('web_nnue_move_feature_id', 'number', ['number', 'number', 'number'])
};
let engineWorker;
let engineBusy = false;
let engineSearchSfen = '';
let autoplayBusy = false;
let autoplaySearchSfen = '';

const board = document.querySelector('#board');
const status = document.querySelector('#status');
const sfen = document.querySelector('#sfen');
let selected = -1;
let selectedDrop = 0;
let gpuNnue = null;
let nnueScore = null;
let evaluationSerial = 0;
let evaluationBusy = false;
let pendingEvaluation = null;
let flipped = false;
let lastMove = -1;
let engineInfo = '';
let pendingPromotion = [];
let nnueMoveBusy = false;
let previousResult = 0;
let focusedVisualSquare = 40;
let engineMoveFrom = -1;
let engineMoveTo = -1;
let engineEffectActive = false;

const names = ['', '歩', '香', '桂', '銀', '金', '角', '飛', '玉', 'と', '杏', '圭', '全', '馬', '龍'];
const handNames = ['歩', '香', '桂', '銀', '金', '角', '飛'];
const strengthNodes = { practice: 64, casual: 128, club: 256, strong: 1024, expert: 4096 };

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
  for (let visualSquare = 0; visualSquare < 81; ++visualSquare) {
    const square = flipped ? 80 - visualSquare : visualSquare;
    const button = document.createElement('button');
    const visualRow = Math.floor(visualSquare / 9);
    const visualColumn = visualSquare % 9;
    const piece = api.pieceAt(square);
    button.className = 'square' + (piece > 0 ? ' black' : piece < 0 ? ' white' : '');
    if (piece && (piece < 0) !== flipped) button.classList.add('upside-down');
    if (square === selected) button.classList.add('selected');
    if (targets.has(square)) button.classList.add('target');
    if (square === lastMove) button.classList.add('last-move');
    if (engineEffectActive && square === engineMoveFrom) button.classList.add('engine-move-origin');
    if (engineEffectActive && square === engineMoveTo) button.classList.add('engine-move-effect');
    button.dataset.square = square;
    button.dataset.visualSquare = visualSquare;
    button.tabIndex = visualSquare === focusedVisualSquare ? 0 : -1;
    const pieceLabel = document.createElement('span');
    pieceLabel.className = 'piece-label';
    pieceLabel.textContent = piece ? names[Math.abs(piece)] : '';
    button.append(pieceLabel);
    if (visualRow === 0) {
      const file = document.createElement('span');
      file.className = 'coordinate coordinate-file';
      file.textContent = squareName(square)[0];
      button.append(file);
    }
    if (visualColumn === 0) {
      const rank = document.createElement('span');
      rank.className = 'coordinate coordinate-rank';
      rank.textContent = squareName(square)[1];
      button.append(rank);
    }
    button.setAttribute('aria-label', `${squareName(square)}${piece ? ` ${names[Math.abs(piece)]}` : ' empty'}`);
    button.addEventListener('focus', () => { focusedVisualSquare = visualSquare; });
    button.addEventListener('click', () => clickSquare(square, moves));
    board.append(button);
  }
  engineEffectActive = false;
  renderHands();
  renderMoveList();
  const result = api.result();
  const turn = result === 0 ? (api.side() === 0 ? 'Black to move' : 'White to move')
    : result === 1 ? 'Black wins' : result === 2 ? 'White wins' : 'Draw';
  status.textContent = turn;
  const score = document.querySelector('#evaluation');
  score.textContent = nnueScore == null ? 'Evaluation: material search' : `NNUE: ${formatScore(nnueScore)} (${api.side() === 0 ? 'Black' : 'White'} perspective)`;
  sfen.value = api.getSfen();
  document.querySelector('#undo').disabled = !api.canUndo();
  document.querySelector('#redo').disabled = !api.canRedo();
  document.querySelector('#engine-move').disabled = engineBusy || autoplayBusy || result !== 0;
  document.querySelector('#engine-cancel').disabled = !engineBusy;
  document.querySelector('#autoplay').disabled = engineBusy || autoplayBusy || result !== 0;
  document.querySelector('#autoplay-cancel').disabled = !autoplayBusy;
  document.querySelector('#nnue-move').disabled = !gpuNnue || nnueMoveBusy || result !== 0;
  document.querySelector('#engine-nodes-value').textContent = document.querySelector('#engine-nodes').value;
  document.querySelector('#engine-info').textContent = engineInfo;
  if (result !== 0 && previousResult === 0) queueMicrotask(showGameResult);
  previousResult = result;
  requestEvaluation();
}

function showGameResult() {
  const result = api.result();
  if (result === 0) return;
  const title = result === 1 ? 'Black wins' : result === 2 ? 'White wins' : 'Draw';
  document.querySelector('#result-title').textContent = title;
  document.querySelector('#result-detail').textContent = result === 3
    ? 'The game ended in a draw.' : `${title}. Start a new game when you are ready.`;
  const dialog = document.querySelector('#result-dialog');
  if (!dialog.open) dialog.showModal();
}

function formatScore(score) { return `${score >= 0 ? '+' : ''}${(score / 100).toFixed(2)}`; }
function formatNps(nps) { return nps >= 1000000 ? `${(nps / 1000000).toFixed(1)}M` : nps >= 1000 ? `${(nps / 1000).toFixed(1)}k` : `${nps}`; }

function currentFeatures(perspective) {
  const count = api.nnueFeatureCount(perspective);
  return Array.from({ length: count }, (_, index) => api.nnueFeatureId(perspective, index));
}

function moveFeatures(moveIndex, perspective) {
  const count = api.nnueMoveFeatureCount(moveIndex, perspective);
  return Array.from({ length: count }, (_, index) => api.nnueMoveFeatureId(moveIndex, perspective, index));
}

function squareName(square) {
  const file = 9 - (square % 9);
  return `${file}${String.fromCharCode(97 + Math.floor(square / 9))}`;
}

function moveLabel(move) {
  return move.from === 255 ? `${handNames[move.drop - 1]}*${squareName(move.to)}`
    : `${squareName(move.from)}–${squareName(move.to)}${move.promotes ? '+' : ''}`;
}

function renderMoveList() {
  const list = document.querySelector('#moves');
  list.replaceChildren();
  const currentPly = api.historyCount();
  const timelineCount = api.timelineCount();
  for (let index = 0; index < timelineCount; index += 2) {
    const row = document.createElement('li');
    const number = document.createElement('span');
    number.textContent = `${index / 2 + 1}.`;
    row.append(number, timelineButton(index, currentPly));
    if (index + 1 < timelineCount) row.append(timelineButton(index + 1, currentPly));
    list.append(row);
  }
  if (!list.childElementCount) list.innerHTML = '<li class="empty-moves">No moves yet</li>';
  list.scrollTop = list.scrollHeight;
}

function timelineButton(ply, currentPly) {
  const button = document.createElement('button');
  button.className = 'timeline-move' + (ply + 1 === currentPly ? ' current' : '') + (ply >= currentPly ? ' future' : '');
  button.dataset.ply = ply;
  button.textContent = api.timelineMove(ply);
  button.title = `Jump to ply ${ply + 1}`;
  return button;
}

function goToPly(targetPly) {
  if (targetPly < 0 || targetPly > api.timelineCount()) return;
  while (api.historyCount() > targetPly) api.undo();
  while (api.historyCount() < targetPly) api.redo();
  engineInfo = '';
  lastMove = targetPly === 0 ? -1 : usiDestination(api.timelineMove(targetPly - 1));
  selected = -1; selectedDrop = 0;
  render();
}

function usiPositionCommand() {
  const moves = Array.from({ length: api.historyCount() }, (_, index) => api.timelineMove(index));
  return `position sfen ${api.getRootSfen()}${moves.length ? ` moves ${moves.join(' ')}` : ''}`;
}

async function copyText(text, description) {
  try {
    if (navigator.clipboard?.writeText) await navigator.clipboard.writeText(text);
    else {
      const copySource = document.createElement('textarea');
      copySource.value = text; copySource.style.position = 'fixed'; copySource.style.opacity = '0';
      document.body.append(copySource); copySource.select();
      if (!document.execCommand('copy')) throw new Error('clipboard access was denied');
      copySource.remove();
    }
    document.querySelector('#export-state').textContent = `${description} copied.`;
  } catch (error) {
    document.querySelector('#export-state').textContent = `Could not copy: ${error.message || error}`;
  }
}

function requestEvaluation() {
  const serial = ++evaluationSerial;
  if (!gpuNnue) return;
  pendingEvaluation = { serial, evaluator: gpuNnue, features: currentFeatures(api.side()), perspective: api.side() };
  if (!evaluationBusy) void flushEvaluation();
}

async function flushEvaluation() {
  evaluationBusy = true;
  while (pendingEvaluation) {
    const request = pendingEvaluation;
    pendingEvaluation = null;
    try {
      const score = await request.evaluator.evaluate(request.features, request.perspective);
      if (request.serial === evaluationSerial && request.evaluator === gpuNnue) {
        nnueScore = score;
        document.querySelector('#evaluation').textContent = `NNUE: ${formatScore(score)} (${request.perspective === 0 ? 'Black' : 'White'} perspective)`;
      }
    } catch (error) {
      if (request.serial === evaluationSerial && request.evaluator === gpuNnue) {
        gpuNnue.dispose(); gpuNnue = null; nnueScore = null;
        document.querySelector('#nnue-state').textContent = `NNUE disabled: ${error.message}`;
      }
    }
  }
  evaluationBusy = false;
  if (pendingEvaluation) void flushEvaluation();
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
      button.disabled = color !== api.side() || count === 0 || engineOwnsTurn();
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
  if (engineOwnsTurn()) return;
  const candidates = moves.filter(candidate => candidate.to === square && (selectedDrop
    ? candidate.from === 255 && candidate.drop === selectedDrop
    : candidate.from === selected));
  if (candidates.length > 0) {
    if (candidates.length > 1) {
      pendingPromotion = candidates;
      document.querySelector('#promotion-dialog').showModal();
      return;
    }
    playMove(candidates[0]);
    return;
  }
  if (selectedDrop) { selectedDrop = 0; render(); return; }
  const piece = api.pieceAt(square);
  if (piece && (piece > 0) === (api.side() === 0)) selected = square;
  else selected = -1;
  render();
}

function playMove(move) {
  if (move && api.play(move.index)) {
    lastMove = move.to;
    focusedVisualSquare = flipped ? 80 - move.to : move.to;
  }
  engineMoveFrom = -1;
  engineMoveTo = -1;
  engineEffectActive = false;
  selected = -1; selectedDrop = 0; engineInfo = '';
  render();
  maybeStartEngineMove();
}

function refresh() { selected = -1; selectedDrop = 0; lastMove = -1; engineMoveFrom = -1; engineMoveTo = -1; engineEffectActive = false; render(); }
document.querySelector('#reset').addEventListener('click', () => { api.reset(); engineInfo = ''; refresh(); maybeStartEngineMove(); });
document.querySelector('#undo').addEventListener('click', () => { if (api.undo()) { engineInfo = ''; refresh(); } });
document.querySelector('#redo').addEventListener('click', () => { if (api.redo()) { engineInfo = ''; refresh(); } });
document.querySelector('#load-sfen').addEventListener('click', () => {
  if (!api.setSfen(sfen.value.trim())) {
    window.alert('Invalid SFEN');
    return;
  }
  engineInfo = '';
  refresh();
  maybeStartEngineMove();
});
document.querySelector('#copy-sfen').addEventListener('click', () => copyText(api.getSfen(), 'SFEN'));
document.querySelector('#copy-usi').addEventListener('click', () => copyText(usiPositionCommand(), 'USI position command'));
document.querySelector('#flip-board').addEventListener('click', () => { flipped = !flipped; render(); });
document.querySelector('#engine-nodes').addEventListener('input', () => {
  document.querySelector('#engine-strength').value = 'custom';
  render();
});
document.querySelector('#engine-strength').addEventListener('change', event => {
  const nodes = strengthNodes[event.target.value];
  if (nodes) document.querySelector('#engine-nodes').value = nodes;
  engineInfo = nodes ? `${event.target.options[event.target.selectedIndex].text}: ${nodes} node search budget.` : '';
  render();
});
for (const choice of document.querySelectorAll('[data-promotion]')) {
  choice.addEventListener('click', () => {
    const promote = choice.dataset.promotion === 'yes';
    const move = pendingPromotion.find(candidate => Boolean(candidate.promotes) === promote);
    document.querySelector('#promotion-dialog').close();
    playMove(move);
    pendingPromotion = [];
  });
}
document.querySelector('#promotion-dialog').addEventListener('close', () => { pendingPromotion = []; });
document.querySelector('#result-new-game').addEventListener('click', () => {
  document.querySelector('#result-dialog').close();
  api.reset(); engineInfo = ''; refresh(); maybeStartEngineMove();
});
document.querySelector('#nnue-model').addEventListener('change', async event => {
  const file = event.target.files[0];
  if (!file) return;
  if (file.name.toLowerCase().endsWith('.bin')) {
    const state = document.querySelector('#nnue-state');
    state.textContent = `Loading ${file.name} into the WASM engine…`;
    engineWorker.terminate();
    engineBusy = false;
    autoplayBusy = false;
    engineSearchSfen = '';
    autoplaySearchSfen = '';
    engineWorker = createEngineWorker();
    const buffer = await file.arrayBuffer();
    engineWorker.postMessage({ mode: 'load-model', buffer }, [buffer]);
    return;
  }
  const state = document.querySelector('#nnue-state');
  state.textContent = `Loading ${file.name} onto WebGPU…`;
  const previous = gpuNnue;
  let evaluator = null;
  try {
    evaluator = new WebGpuNnue();
    const description = await evaluator.load(await file.arrayBuffer());
    gpuNnue = evaluator; nnueScore = null;
    if (previous) previous.dispose();
    state.textContent = `WebGPU NNUE active — ${description}`;
    requestEvaluation();
  } catch (error) {
    if (evaluator) evaluator.dispose();
    state.textContent = previous
      ? `New NNUE model rejected: ${error.message}. The current model remains active.`
      : `NNUE unavailable: ${error.message}`;
  }
});
function configuredEngineSide() {
  const value = document.querySelector('#engine-side').value;
  return value === '' ? -1 : Number(value);
}

function engineOwnsTurn() {
  return engineBusy || autoplayBusy || (api.result() === 0 && configuredEngineSide() === api.side());
}

function startEngineMove() {
  if (engineBusy || autoplayBusy || api.result() !== 0) return;
  engineBusy = true;
  engineSearchSfen = api.getSfen();
  engineInfo = 'Engine is searching…';
  render();
  engineWorker.postMessage({ sfen: engineSearchSfen, nodes: Number(document.querySelector('#engine-nodes').value) });
}

function maybeStartEngineMove() {
  if (!engineBusy && api.result() === 0 && configuredEngineSide() === api.side()) startEngineMove();
}

document.querySelector('#engine-move').addEventListener('click', startEngineMove);
document.querySelector('#engine-cancel').addEventListener('click', () => {
  if (!engineBusy) return;
  engineWorker.terminate();
  engineWorker = createEngineWorker();
  engineBusy = false;
  engineSearchSfen = '';
  engineInfo = 'Engine search cancelled.';
  render();
});
document.querySelector('#autoplay').addEventListener('click', () => {
  if (engineBusy || autoplayBusy || api.result() !== 0) return;
  autoplayBusy = true;
  autoplaySearchSfen = api.getSfen();
  engineInfo = 'Auto-play is running up to 1,000 plies…';
  render();
  engineWorker.postMessage({ mode: 'autoplay', sfen: autoplaySearchSfen,
    nodes: Number(document.querySelector('#engine-nodes').value), maxPlies: 1000 });
});
document.querySelector('#autoplay-cancel').addEventListener('click', () => {
  if (!autoplayBusy) return;
  engineWorker.terminate();
  engineWorker = createEngineWorker();
  autoplayBusy = false;
  autoplaySearchSfen = '';
  engineInfo = 'Auto-play cancelled.';
  render();
});
document.querySelector('#engine-side').addEventListener('change', () => {
  engineInfo = configuredEngineSide() < 0 ? '' : `Engine plays ${configuredEngineSide() === 0 ? 'Black' : 'White'}.`;
  render();
  maybeStartEngineMove();
});
document.querySelector('#moves').addEventListener('click', event => {
  const move = event.target.closest('.timeline-move');
  if (move) goToPly(Number(move.dataset.ply) + 1);
});
board.addEventListener('keydown', event => {
  const current = event.target.closest('.square');
  if (!current) return;
  const visualSquare = Number(current.dataset.visualSquare);
  const row = Math.floor(visualSquare / 9);
  const column = visualSquare % 9;
  let next = -1;
  if (event.key === 'ArrowUp' && row > 0) next = visualSquare - 9;
  if (event.key === 'ArrowDown' && row < 8) next = visualSquare + 9;
  if (event.key === 'ArrowLeft' && column > 0) next = visualSquare - 1;
  if (event.key === 'ArrowRight' && column < 8) next = visualSquare + 1;
  if (next >= 0) {
    event.preventDefault();
    focusedVisualSquare = next;
    board.querySelector(`[data-visual-square="${next}"]`).focus();
  }
});
document.querySelector('#nnue-move').addEventListener('click', async () => {
  if (!gpuNnue || nnueMoveBusy || api.result() !== 0) return;
  const evaluator = gpuNnue;
  const rootSfen = api.getSfen();
  const perspective = api.side();
  const moves = legalMoves();
  let playedMove = false;
  nnueMoveBusy = true;
  engineInfo = `NNUE is scoring ${moves.length} legal moves…`;
  render();
  try {
    let bestMove = null;
    let bestScore = -Infinity;
    for (let index = 0; index < moves.length; ++index) {
      if (evaluator !== gpuNnue || rootSfen !== api.getSfen()) return;
      const score = await evaluator.evaluate(moveFeatures(moves[index].index, perspective), perspective);
      if (score > bestScore) { bestScore = score; bestMove = moves[index]; }
      document.querySelector('#engine-info').textContent = `NNUE: ${index + 1}/${moves.length} legal moves`;
    }
    if (!bestMove || evaluator !== gpuNnue || rootSfen !== api.getSfen()) return;
    if (!api.play(bestMove.index)) throw new Error('chosen NNUE move is no longer legal');
    playedMove = true;
    lastMove = bestMove.to;
    engineMoveFrom = bestMove.from === 255 ? -1 : bestMove.from;
    engineMoveTo = bestMove.to;
    engineEffectActive = true;
    engineInfo = `NNUE 1-ply: ${moveLabel(bestMove)} · ${formatScore(bestScore)}`;
  } catch (error) {
    engineInfo = `NNUE move failed: ${error.message}`;
  } finally {
    nnueMoveBusy = false;
    selected = -1; selectedDrop = 0;
    render();
    if (playedMove) maybeStartEngineMove();
  }
});
function createEngineWorker() {
  const worker = new Worker(new URL('./engine-worker.js', import.meta.url), { type: 'module' });
  worker.onmessage = event => {
    if (event.data.model) {
      const state = document.querySelector('#nnue-state');
      if (event.data.error || !event.data.nnue) {
        state.textContent = event.data.error || 'WASM NNUE model rejected; material evaluation remains active.';
        engineInfo = 'WASM NNUE unavailable; using material evaluation.';
      } else {
        state.textContent = 'WASM NNUE active for engine search.';
        engineInfo = 'WASM NNUE model loaded.';
      }
      render();
      maybeStartEngineMove();
      return;
    }
    if (event.data.autoplay) {
      autoplayBusy = false;
      const stale = autoplaySearchSfen !== api.getSfen();
      autoplaySearchSfen = '';
      if (event.data.error) {
        engineInfo = `Auto-play failed: ${event.data.error}`;
        render();
        return;
      }
      if (stale) {
        engineInfo = 'Auto-play result discarded because the position changed.';
        render();
        return;
      }
      let applied = 0;
      const moves = event.data.moves || [];
      for (const move of moves) {
        if (!api.playUsi(move)) break;
        applied++;
      }
      if (applied !== moves.length) {
        engineInfo = `Auto-play stopped: could not apply move ${applied + 1}.`;
        refresh();
        return;
      }
      if (moves.length) {
        lastMove = usiDestination(moves[moves.length - 1]);
        engineMoveFrom = usiOrigin(moves[moves.length - 1]);
        engineMoveTo = lastMove;
        engineEffectActive = true;
        focusedVisualSquare = flipped ? 80 - lastMove : lastMove;
      }
      const reason = event.data.reason === 'move-limit' ? '1,000-ply limit' :
        event.data.reason === 'search-error' ? 'search error' :
        event.data.reason === 'black-wins' ? 'Black wins' :
        event.data.reason === 'white-wins' ? 'White wins' :
        event.data.reason === 'draw' ? 'draw' : 'terminal position';
      engineInfo = `${event.data.nnue ? 'WASM NNUE' : 'Material'} auto-play: ${applied} plies · stopped by ${reason}.`;
      render();
      return;
    }
    engineBusy = false;
    const stale = engineSearchSfen !== api.getSfen();
    engineSearchSfen = '';
    if (stale) {
      engineInfo = 'Engine result discarded because the position changed.';
      render();
      maybeStartEngineMove();
      return;
    }
    if (event.data.error || !event.data.move || !api.playUsi(event.data.move)) {
      window.alert(event.data.error || 'Engine search failed');
      refresh();
    } else {
      engineInfo = `${event.data.nnue ? 'WASM NNUE' : 'Material'} engine: ${event.data.move} · depth ${event.data.depth} · ${event.data.nodes} nodes · ${event.data.timeMs} ms · ${formatNps(event.data.nps)} N/s · ${formatScore(event.data.score)}`;
      lastMove = usiDestination(event.data.move);
      engineMoveFrom = usiOrigin(event.data.move);
      engineMoveTo = lastMove;
      engineEffectActive = true;
      focusedVisualSquare = flipped ? 80 - lastMove : lastMove;
      selected = -1; selectedDrop = 0; render();
    }
  };
  worker.onerror = event => {
    engineBusy = false;
    autoplayBusy = false;
    engineSearchSfen = '';
    autoplaySearchSfen = '';
    engineInfo = `Engine worker failed: ${event.message || 'unknown error'}`;
    render();
  };
  return worker;
}

function usiDestination(move) {
  if (!move || move.length < 4) return -1;
  return (move.charCodeAt(3) - 97) * 9 + 9 - Number(move[2]);
}
function usiOrigin(move) {
  if (!move || move.length < 4 || move[1] === '*') return -1;
  return (move.charCodeAt(1) - 97) * 9 + 9 - Number(move[0]);
}
document.addEventListener('keydown', event => {
  if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 'z') {
    event.preventDefault();
    if (event.shiftKey ? api.redo() : api.undo()) { engineInfo = ''; refresh(); }
  }
});
api.init();
engineWorker = createEngineWorker();
document.querySelector('#nnue-state').textContent = WebGpuNnue.available()
  ? 'Upload nn.bin for WASM NNUE, or .nnue for WebGPU evaluation.'
  : 'Upload nn.bin for WASM NNUE; otherwise engine moves use material evaluation.';
render();
}

main().catch(error => {
  const message = `Unable to start tinyshogi: ${error.message || error}`;
  document.querySelector('#status').textContent = message;
  document.querySelector('#evaluation').textContent = 'Check that the WASM files are served over HTTP.';
  console.error(error);
});
