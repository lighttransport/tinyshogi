const FEATURE_COUNT = 81 * 28 * 81 + 2 * 7 * 19;
function i16(bytes, offset, count) {
  return new Int16Array(bytes.slice(offset, offset + count * 2));
}

function parseModel(bytes) {
  if (!(bytes instanceof ArrayBuffer) || bytes.byteLength < 5) throw new Error('NNUE model is truncated');
  const view = new DataView(bytes);
  const magic = new TextDecoder().decode(bytes.slice(0, 5));
  if (!['NNUE1', 'NNUE2', 'NNUE3'].includes(magic)) throw new Error('Not a tinyshogi NNUE model');
  let offset = 5;
  const need = count => {
    if (!Number.isSafeInteger(count) || count < 0 || offset + count > bytes.byteLength)
      throw new Error('NNUE model is truncated');
  };
  const u32 = () => { need(4); const n = view.getUint32(offset, true); offset += 4; return n; };
  const i32 = () => { need(4); const n = view.getInt32(offset, true); offset += 4; return n; };
  const version = u32(), featureCount = u32(), hidden = u32();
  if (featureCount !== FEATURE_COUNT || hidden === 0 || hidden > 4096) throw new Error('Unsupported NNUE dimensions');
  let headDim = 0;
  if (magic === 'NNUE3') {
    if (version !== 3) throw new Error('Unsupported NNUE metadata');
    headDim = u32();
    if (u32() !== 2 || headDim === 0 || headDim > 128) throw new Error('Unsupported NNUE3 heads');
    const featureScale = i32(), headScale = i32(), outputScale = i32();
    if (featureScale !== 256 || headScale !== 256 || outputScale !== 1024)
      throw new Error('Unsupported NNUE3 scales');
    const activationClip = i32(), headClip = i32();
    const featureOffset = offset, featureBytes = featureCount * hidden * 2;
    need(featureBytes);
    offset += featureBytes;
    const headWeightCount = 2 * headDim * hidden;
    need(headWeightCount * 2);
    const headWeights = i16(bytes, offset, headWeightCount); offset += headWeightCount * 2;
    const headBias = [];
    for (let n = 0; n < 2 * headDim; ++n) { need(8); headBias.push(view.getBigInt64(offset, true)); offset += 8; }
    need(2 * headDim * 2);
    const finalWeights = i16(bytes, offset, 2 * headDim); offset += 2 * headDim * 2;
    need(16);
    const finalBias = [view.getBigInt64(offset, true), view.getBigInt64(offset + 8, true)];
    return { magic, hidden, featureOffset, featureBytes, headDim, headWeights, headBias, finalWeights, finalBias, activationClip, headClip };
  }
  if (version !== (magic === 'NNUE1' ? 1 : 2) || u32() !== 2)
    throw new Error('Unsupported NNUE metadata');
  const featureScale = i32(), outputScale = i32();
  if (featureScale <= 0 || outputScale <= 0) throw new Error('Invalid NNUE scales');
  const activationClip = magic === 'NNUE2' ? i32() : 0x7fffffff;
  const featureOffset = offset, featureBytes = featureCount * hidden * 2;
  need(featureBytes);
  offset += featureBytes;
  need(hidden * 2 * 2 + 4);
  const outputWeights = i16(bytes, offset, hidden * 2); offset += hidden * 2 * 2;
  return { magic, hidden, featureOffset, featureBytes, outputWeights, outputBias: view.getInt32(offset, true), featureScale, outputScale, activationClip };
}

function packFeatureRows(bytes, model) {
  const wordsPerRow = Math.ceil(model.hidden / 2);
  if ((model.hidden & 1) === 0) {
    /* NNUE headers are not four-byte aligned (NNUE1 starts weights at byte
     * 29, NNUE2 at 33, and NNUE3 at 45). GPUQueue.writeBuffer requires an
     * aligned source offset, so make an aligned copy even though row packing
     * itself is already correct for even hidden dimensions. */
    const data = new Uint32Array(bytes.slice(model.featureOffset,
      model.featureOffset + model.featureBytes));
    return { data, byteLength: data.byteLength, wordsPerRow };
  }
  const source = new DataView(bytes, model.featureOffset, model.featureBytes);
  const packed = new Uint32Array(FEATURE_COUNT * wordsPerRow);
  for (let feature = 0; feature < FEATURE_COUNT; ++feature) {
    const sourceRow = feature * model.hidden * 2;
    const targetRow = feature * wordsPerRow;
    for (let word = 0; word < wordsPerRow; ++word) {
      const lowIndex = word * 2;
      const low = source.getUint16(sourceRow + lowIndex * 2, true);
      const high = lowIndex + 1 < model.hidden ? source.getUint16(sourceRow + (lowIndex + 1) * 2, true) : 0;
      packed[targetRow + word] = low | (high << 16);
    }
  }
  return { data: packed, byteLength: packed.byteLength, wordsPerRow };
}

const shader = /* wgsl */`
struct Params { count: u32, hidden: u32 }
@group(0) @binding(0) var<storage, read> weights: array<u32>;
@group(0) @binding(1) var<storage, read> ids: array<u32>;
@group(0) @binding(2) var<storage, read_write> sums: array<i32>;
@group(0) @binding(3) var<uniform> params: Params;
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  let unit = gid.x;
  if (unit >= params.hidden) { return; }
  var total: i32 = 0;
  let word = unit / 2u;
  let high = (unit & 1u) != 0u;
  for (var n: u32 = 0u; n < params.count; n++) {
    let packed = weights[ids[n] * ((params.hidden + 1u) / 2u) + word];
    total += select(bitcast<i32>(packed << 16u) >> 16, bitcast<i32>(packed) >> 16, high);
  }
  sums[unit] = total;
}`;

export class WebGpuNnue {
  static available() { return typeof navigator !== 'undefined' && !!navigator.gpu; }

  async load(bytes) {
    if (!WebGpuNnue.available()) throw new Error('WebGPU is not available in this browser');
    const model = parseModel(bytes);
    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) throw new Error('No WebGPU adapter is available');
    const device = await adapter.requestDevice();
    const featureUpload = packFeatureRows(bytes, model);
    if (featureUpload.byteLength > device.limits.maxStorageBufferBindingSize) {
      throw new Error(`Model needs ${(featureUpload.byteLength / 1048576).toFixed(0)} MiB GPU storage; this adapter allows ${(device.limits.maxStorageBufferBindingSize / 1048576).toFixed(0)} MiB`);
    }
    this.device = device;
    this.model = model;
    this.evaluationTail = Promise.resolve();
    device.pushErrorScope('validation');
    try {
      const storage = GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST;
      this.weightBuffer = device.createBuffer({ size: featureUpload.byteLength, usage: storage });
      device.queue.writeBuffer(this.weightBuffer, 0, featureUpload.data);
      this.idBuffer = device.createBuffer({ size: 128 * 4, usage: storage });
      this.sumBuffer = device.createBuffer({ size: model.hidden * 4, usage: storage | GPUBufferUsage.COPY_SRC });
      this.readBuffer = device.createBuffer({ size: model.hidden * 4, usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ });
      this.paramBuffer = device.createBuffer({ size: 8, usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST });
      const module = device.createShaderModule({ code: shader });
      this.pipeline = device.createComputePipeline({ layout: 'auto', compute: { module, entryPoint: 'main' } });
      this.bindGroup = device.createBindGroup({ layout: this.pipeline.getBindGroupLayout(0), entries: [
        { binding: 0, resource: { buffer: this.weightBuffer } }, { binding: 1, resource: { buffer: this.idBuffer } },
        { binding: 2, resource: { buffer: this.sumBuffer } }, { binding: 3, resource: { buffer: this.paramBuffer } }
      ] });
    } catch (error) {
      await device.popErrorScope();
      this.dispose();
      throw error;
    }
    const validationError = await device.popErrorScope();
    if (validationError) {
      this.dispose();
      throw new Error(`WebGPU validation failed: ${validationError.message}`);
    }
    device.lost.then(info => { this.failure = `WebGPU device lost: ${info.message || info.reason}`; });
    return `${model.magic}, ${model.hidden} hidden units`;
  }

  evaluate(featureIds, perspective) {
    const evaluation = this.evaluationTail.then(() => this.evaluateNow(featureIds, perspective));
    this.evaluationTail = evaluation.catch(() => {});
    return evaluation;
  }

  dispose() {
    for (const buffer of [this.weightBuffer, this.idBuffer, this.sumBuffer, this.readBuffer, this.paramBuffer]) {
      if (buffer) buffer.destroy();
    }
    this.weightBuffer = null;
    this.idBuffer = null;
    this.sumBuffer = null;
    this.readBuffer = null;
    this.paramBuffer = null;
    this.device = null;
    this.failure = 'NNUE evaluator was released';
  }

  async evaluateNow(featureIds, perspective) {
    if (!this.device || this.failure) throw new Error(this.failure || 'No NNUE model loaded');
    if (featureIds.length > 128) throw new Error('Too many NNUE features');
    const ids = new Uint32Array(128); ids.set(featureIds);
    this.device.queue.writeBuffer(this.idBuffer, 0, ids);
    this.device.queue.writeBuffer(this.paramBuffer, 0, new Uint32Array([featureIds.length, this.model.hidden]));
    const encoder = this.device.createCommandEncoder();
    const pass = encoder.beginComputePass(); pass.setPipeline(this.pipeline); pass.setBindGroup(0, this.bindGroup);
    pass.dispatchWorkgroups(Math.ceil(this.model.hidden / 64)); pass.end();
    encoder.copyBufferToBuffer(this.sumBuffer, 0, this.readBuffer, 0, this.model.hidden * 4);
    this.device.queue.submit([encoder.finish()]);
    await this.readBuffer.mapAsync(GPUMapMode.READ);
    const sum = new Int32Array(this.readBuffer.getMappedRange().slice(0)); this.readBuffer.unmap();
    return this.score(sum, perspective);
  }

  score(sum, perspective) {
    const m = this.model;
    if (m.magic !== 'NNUE3') {
      let raw = BigInt(m.outputBias) * BigInt(m.featureScale);
      const base = perspective * m.hidden;
      for (let i = 0; i < m.hidden; ++i) raw += BigInt(Math.min(Math.max(sum[i], 0), m.activationClip)) * BigInt(m.outputWeights[base + i]);
      return Math.round(Math.tanh(Number(raw) / (m.featureScale * m.outputScale)) * 1000);
    }
    let raw = m.finalBias[perspective];
    for (let head = 0; head < m.headDim; ++head) {
      let value = m.headBias[perspective * m.headDim + head];
      const base = (perspective * m.headDim + head) * m.hidden;
      for (let i = 0; i < m.hidden; ++i) value += BigInt(Math.min(Math.max(sum[i], 0), m.activationClip)) * BigInt(m.headWeights[base + i]);
      let activated = value > 0n ? Number((value + 128n) >> 8n) : 0;
      activated = Math.min(activated, m.headClip);
      raw += BigInt(activated) * BigInt(m.finalWeights[perspective * m.headDim + head]);
    }
    return Math.round(Math.tanh(Number(raw) / (256 * 1024)) * 1000);
  }
}
