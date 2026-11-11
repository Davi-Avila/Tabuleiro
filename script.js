'use strict';

/* =====================================================================
 *  SIMULADOR DE QUADRO DE GALTON
 *
 *  IDEIA CENTRAL
 *  -------------
 *  O quadro tem R fileiras de pinos. A bolinha bate em um pino por fileira,
 *  então ela toma exatamente R decisões independentes:
 *      0 = esquerda, 1 = direita   (cada uma com probabilidade 1/2)
 *  O compartimento final é a SOMA das decisões "direita":
 *      compartimento = d1 + d2 + ... + dR   ->  Binomial(R, 1/2)
 *  Média = R/2 e variância = R/4 (desvio padrão = sqrt(R)/2).
 *  Pelo Teorema Central do Limite, essa binomial se aproxima de uma
 *  Normal N(R/2, R/4) quando R e o número de bolinhas crescem.
 *
 *  O compartimento NUNCA é sorteado diretamente: ele surge da trajetória.
 *
 *  UNIDADES
 *  --------
 *  Toda a física roda em "unidades de quadro": a distância horizontal entre
 *  dois pinos vizinhos da mesma fileira vale 1. A origem x = 0 é o centro do
 *  quadro. Na hora de desenhar, essas unidades são convertidas em pixels
 *  por um fator de escala, então o redimensionamento não afeta a simulação.
 * ===================================================================== */

/* ---------------------------------------------------------------------
 *  Configuração
 * ------------------------------------------------------------------- */
const CONFIG = {
  ROW_SPACING: Math.sqrt(3) / 2,   // distância vertical entre fileiras (malha triangular)
  PIN_RADIUS: 0.10,
  BALL_RADIUS: 0.17,               // 2 * 0.17 = 0,34 < espaço livre entre pinos (0,8)

  FIRST_PIN_Y: 1.7,                // posição vertical do pino do topo
  FUNNEL_TOP_Y: -1.0,
  FUNNEL_EXIT_Y: 0.6,
  FUNNEL_TOP_HALF_WIDTH: 1.45,
  FUNNEL_EXIT_HALF_WIDTH: 0.32,

  BIN_GAP: 0.95,                   // distância entre o último pino e a boca dos compartimentos
  BIN_HEIGHT: 3.0,
  WALL_HALF: 0.03,                 // meia espessura das divisórias

  SEGMENT_TIME: 0.30,              // segundos (a 1×) para ir de um pino ao seguinte
  MAX_ACTIVE_BALLS: 600,           // limite de bolinhas animadas simultaneamente
  MIN_SPAWN_RATE: 8,               // bolinhas por segundo
  MAX_SPAWN_RATE: 700,
  STATS_REFRESH_MS: 90,

  MIN_ROWS: 6,
  MAX_ROWS: 16,
};

/* ---------------------------------------------------------------------
 *  Estado global da simulação
 * ------------------------------------------------------------------- */
const state = {
  status: 'idle',          // 'idle' | 'running' | 'paused' | 'done'
  rows: 12,                // fileiras de pinos (R); compartimentos = R + 1
  totalBalls: 1000,
  released: 0,             // quantas já entraram no quadro
  finished: 0,             // quantas já caíram em um compartimento
  background: 0,           // quantas foram resolvidas sem animação
  counts: [],              // counts[b] = bolinhas no compartimento b
  maxCount: 0,
  active: [],              // bolinhas sendo animadas
  spawnCredit: 0,          // crédito fracionário de lançamentos
  speed: 1,
  showTheory: true,
};

/* Dimensões e escala atuais (recalculadas em computeLayout) */
const view = {
  dpr: 1, cssW: 0, boardH: 0, histH: 220,
  scale: 30, ox: 0, oy: 0, key: '',
};

const dom = {};            // referências do DOM
let boardCtx, staticCtx, histCtx, staticCanvas;
let staticDirty = true, histDirty = true, statsDirty = true;
let rafId = 0, lastFrameTime = 0, lastStatsTime = 0;

const fmtInt = new Intl.NumberFormat('pt-BR');
const fmtDec = new Intl.NumberFormat('pt-BR', { minimumFractionDigits: 2, maximumFractionDigits: 2 });

/* =====================================================================
 *  GEOMETRIA DO QUADRO (em unidades de quadro)
 * ===================================================================== */

/** x do pino k (0..r) da fileira r: fileira r tem r+1 pinos centrados em x = 0. */
function pinX(r, k) { return k - r / 2; }

/** y do pino da fileira r. */
function pinY(r) { return CONFIG.FIRST_PIN_Y + r * CONFIG.ROW_SPACING; }

/** x do centro do compartimento b. Fica exatamente abaixo do "vão" entre dois pinos da última fileira. */
function binCenterX(b) { return b - state.rows / 2; }

/** Valores verticais que dependem do número de fileiras. */
function geometry() {
  const lastPinY = pinY(state.rows - 1);
  const binTop = lastPinY + CONFIG.BIN_GAP;
  const binBottom = binTop + CONFIG.BIN_HEIGHT;
  return { lastPinY, binTop, binBottom, yMin: CONFIG.FUNNEL_TOP_Y - 0.25, yMax: binBottom + 0.7 };
}

/** Aleatório uniforme em [min, max). */
function randRange(min, max) { return min + Math.random() * (max - min); }

/* =====================================================================
 *  DECISÃO ESQUERDA / DIREITA  (o coração do experimento)
 * ===================================================================== */

/**
 * Executada a cada colisão com um pino.
 * Retorna 0 (esquerda) ou 1 (direita) com probabilidade 1/2 cada.
 * O compartimento final é a soma destes R valores -> Binomial(R, 1/2).
 */
function decideDirection() {
  return Math.random() < 0.5 ? 0 : 1;
}

/* =====================================================================
 *  COMPARTIMENTOS: quanto ocupam e onde a próxima bolinha pousa
 * ===================================================================== */

/**
 * Descreve como o conteúdo dos compartimentos é desenhado.
 * - Poucas bolinhas: pilha de bolinhas individuais ("asBalls").
 * - Muitas bolinhas: barra proporcional à contagem do compartimento mais cheio.
 */
function binMetrics() {
  const innerW = 1 - 2 * CONFIG.WALL_HALF - 0.04;
  const cols = Math.max(1, Math.floor(innerW / (2 * CONFIG.BALL_RADIUS)));
  const rowH = CONFIG.BALL_RADIUS * 1.8;
  const innerH = CONFIG.BIN_HEIGHT - 0.08;
  const capacityRows = Math.floor(innerH / rowH);
  const maxRows = Math.ceil(state.maxCount / cols);
  return { innerW, cols, rowH, innerH, capacityRows, asBalls: maxRows <= capacityRows };
}

/** Altura (em unidades) ocupada pelo compartimento b. */
function binFillHeight(b, m) {
  const count = state.counts[b];
  if (count === 0) return 0;
  if (m.asBalls) return Math.ceil(count / m.cols) * m.rowH;
  return m.innerH * (count / state.maxCount);
}

/** y onde a bolinha deve parar (topo da pilha atual do compartimento). */
function binTargetY(b) {
  const g = geometry();
  const m = binMetrics();
  const floorY = g.binBottom - 0.04;
  const top = floorY - binFillHeight(b, m);
  return Math.max(g.binTop + CONFIG.BALL_RADIUS, top - CONFIG.BALL_RADIUS);
}

/** Registra a chegada de uma bolinha ao compartimento. */
function registerLanding(bin) {
  state.counts[bin] += 1;
  state.finished += 1;
  if (state.counts[bin] > state.maxCount) state.maxCount = state.counts[bin];
  staticDirty = histDirty = statsDirty = true;
}

/* =====================================================================
 *  BOLINHAS ANIMADAS
 *
 *  O movimento é dividido em "segmentos": pino -> pino seguinte.
 *  Em cada segmento a bolinha segue um arco:
 *    - y: queda sob gravidade (com um pequeno quique para cima ao bater no pino)
 *    - x: desloca meia unidade para o lado escolhido, com desaceleração
 *  Como cada segmento começa e termina POUSADO NO TOPO de um pino e se
 *  afasta do pino de origem imediatamente, a bolinha nunca atravessa pinos.
 * ===================================================================== */

/** Cria um segmento de movimento de (x0, y0) até (x1, y1). */
function beginSegment(ball, x1, y1, bounce, easePower) {
  ball.x0 = ball.x1;
  ball.y0 = ball.y1;
  ball.x1 = x1;
  ball.y1 = y1;

  const dy = y1 - ball.y0;                                   // sempre > 0
  // Tempo cresce com a raiz da altura (queda livre) e ganha pequena variação aleatória
  const duration = CONFIG.SEGMENT_TIME * Math.sqrt(dy / CONFIG.ROW_SPACING) * randRange(0.88, 1.12);

  // Escolhe a gravidade g e a velocidade vertical inicial vy0 de modo que
  //   y(T) = y0 + vy0*T + g*T²/2 = y0 + dy   (chega exatamente no alvo)
  // com vy0 = -bounce*dy/T (<= 0 -> pequeno "pulo" ao deixar o pino).
  ball.T = duration;
  ball.g = (2 * dy / (duration * duration)) * (1 + bounce);
  ball.vy0 = -bounce * dy / duration;
  ball.ease = easePower;
  ball.wobble = randRange(-0.035, 0.035);                    // leve variação lateral
}

/** Aponta a bolinha para o topo do pino (ball.r, ball.k), com pequena variação de ponto de contato. */
function aimAtPin(ball, bounce, easePower) {
  const contactJitter = CONFIG.PIN_RADIUS * 0.6;             // mantém o contato na parte de cima do pino
  const x1 = pinX(ball.r, ball.k) + randRange(-contactJitter, contactJitter);
  const y1 = pinY(ball.r) - CONFIG.PIN_RADIUS - CONFIG.BALL_RADIUS;
  beginSegment(ball, x1, y1, bounce, easePower);
}

/** Aponta a bolinha para dentro do compartimento ball.bin. */
function aimAtBin(ball) {
  const x1 = binCenterX(ball.bin) + randRange(-0.1, 0.1);
  beginSegment(ball, x1, binTargetY(ball.bin), 0.6, 3);
}

/** Cria uma bolinha animada saindo do funil. */
function spawnAnimatedBall(initialAdvance) {
  const ball = {
    stage: 'toPin',      // 'toPin' (indo até um pino) | 'toBin' (indo ao compartimento)
    r: 0, k: 0, bin: 0,  // pino-alvo atual
    x: 0, y: 0, x0: 0, y0: 0,
    x1: randRange(-0.1, 0.1),                  // posição inicial dentro do funil
    y1: -0.45,
    T: 1, g: 0, vy0: 0, ease: 1, wobble: 0,
    tau: initialAdvance,                       // tempo decorrido no segmento atual
  };
  aimAtPin(ball, 0, 1);                        // queda livre do funil até o pino do topo
  updateBallPosition(ball);
  state.active.push(ball);
}

/** Calcula x,y da bolinha em função do tempo decorrido no segmento. */
function updateBallPosition(ball) {
  const u = Math.min(1, ball.tau / ball.T);                  // progresso 0..1
  const horizontal = 1 - Math.pow(1 - u, ball.ease);         // desacelera no fim
  ball.x = ball.x0 + (ball.x1 - ball.x0) * horizontal + ball.wobble * Math.sin(Math.PI * u);
  ball.y = ball.y0 + ball.vy0 * ball.tau + 0.5 * ball.g * ball.tau * ball.tau;
}

/**
 * Chamada quando a bolinha termina um segmento.
 * Retorna true se ela continua em jogo, false se pousou.
 */
function completeSegment(ball) {
  if (ball.stage === 'toPin') {
    // COLISÃO com o pino (ball.r, ball.k): decide esquerda (0) ou direita (1).
    const direction = decideDirection();

    if (ball.r < state.rows - 1) {
      // Vai para o pino da fileira seguinte:
      //   esquerda -> pino k   | direita -> pino k+1
      // (cada pino tem dois "filhos" abaixo, como no esquema triangular)
      ball.r += 1;
      ball.k += direction;
      aimAtPin(ball, randRange(0.7, 1.3), 2);
      return true;
    }

    // Último pino: o compartimento é o número de decisões "direita" acumuladas (ball.k + direction)
    ball.bin = ball.k + direction;
    ball.stage = 'toBin';
    aimAtBin(ball);
    return true;
  }

  registerLanding(ball.bin);
  return false;
}

/** Avança todas as bolinhas animadas em `dt` segundos de simulação. */
function advanceBalls(dt) {
  const list = state.active;
  let write = 0;
  for (let i = 0; i < list.length; i++) {
    const ball = list[i];
    ball.tau += dt;
    let alive = true;
    // while: em quadros longos uma bolinha pode cruzar mais de um segmento
    while (ball.tau >= ball.T) {
      ball.tau -= ball.T;
      if (!completeSegment(ball)) { alive = false; break; }
    }
    if (alive) {
      updateBallPosition(ball);
      list[write++] = ball;
    }
  }
  list.length = write;
}

/* =====================================================================
 *  LANÇAMENTO DAS BOLINHAS (desempenho)
 * ===================================================================== */

/** Bolinhas por segundo (a 1×): maior para totais maiores, para durar ~10-15 s. */
function spawnRate() {
  const rate = state.totalBalls / 10;
  return Math.min(CONFIG.MAX_SPAWN_RATE, Math.max(CONFIG.MIN_SPAWN_RATE, rate));
}

/**
 * Resolve uma bolinha SEM animar, mas pelo mesmo processo:
 * R decisões esquerda/direita independentes, somadas.
 * Por isso a distribuição continua exatamente binomial.
 */
function resolveWithoutAnimation() {
  let bin = 0;
  for (let row = 0; row < state.rows; row++) bin += decideDirection();
  registerLanding(bin);
  state.background += 1;
}

/** Lança as bolinhas devidas neste quadro. */
function releaseBalls(dt) {
  const remaining = state.totalBalls - state.released;
  if (remaining <= 0) return;

  state.spawnCredit += spawnRate() * dt;
  const toRelease = Math.min(Math.floor(state.spawnCredit), remaining);
  state.spawnCredit -= toRelease;

  for (let i = 0; i < toRelease; i++) {
    if (state.active.length < CONFIG.MAX_ACTIVE_BALLS) {
      spawnAnimatedBall(Math.random() * dt);   // espalha as entradas dentro do quadro
    } else {
      resolveWithoutAnimation();
    }
    state.released += 1;
  }
  statsDirty = true;
}

/* =====================================================================
 *  PASSO DA SIMULAÇÃO
 * ===================================================================== */

function stepSimulation(dt) {
  releaseBalls(dt);
  advanceBalls(dt);

  if (state.released >= state.totalBalls && state.active.length === 0) {
    state.status = 'done';
    statsDirty = histDirty = staticDirty = true;
    syncUI();
  }
}

/* =====================================================================
 *  ESTATÍSTICAS
 * ===================================================================== */

/** Média, desvio padrão (populacional) e moda dos compartimentos já preenchidos. */
function computeStats() {
  const n = state.finished;
  let sum = 0;
  let modeBin = -1;
  let modeCount = 0;
  for (let b = 0; b < state.counts.length; b++) {
    const c = state.counts[b];
    sum += b * c;
    if (c > modeCount) { modeCount = c; modeBin = b; }
  }
  if (n === 0) return { n, mean: NaN, sd: NaN, modeBin, modeCount };

  const mean = sum / n;
  let sq = 0;
  for (let b = 0; b < state.counts.length; b++) sq += state.counts[b] * (b - mean) * (b - mean);
  return { n, mean, sd: Math.sqrt(sq / n), modeBin, modeCount };
}

function updateStatsDisplay() {
  const s = computeStats();
  const R = state.rows;
  const total = state.status === 'idle' ? Number(dom.ballsRange.value) : state.totalBalls;
  const progress = total > 0 ? Math.min(100, (s.n / total) * 100) : 0;

  dom.statTotal.textContent = fmtInt.format(total);
  dom.statDone.textContent = fmtInt.format(s.n);
  dom.statActive.textContent = fmtInt.format(state.active.length);
  dom.statBackground.textContent = fmtInt.format(state.background);
  dom.statBins.textContent = fmtInt.format(R + 1);
  dom.progressBar.style.width = progress.toFixed(1) + '%';
  dom.progressText.textContent = (progress >= 100 ? '100' : progress.toFixed(1).replace('.', ',')) + '%';

  if (s.n === 0) {
    dom.statMode.textContent = '–';
    dom.statMean.textContent = '–';
    dom.statSd.textContent = '–';
  } else {
    dom.statMode.textContent = `nº ${s.modeBin} (${fmtInt.format(s.modeCount)})`;
    dom.statMean.textContent = `${fmtDec.format(s.mean)}  (teórico ${fmtDec.format(R / 2)})`;
    dom.statSd.textContent = `${fmtDec.format(s.sd)}  (teórico ${fmtDec.format(Math.sqrt(R) / 2)})`;
  }
  statsDirty = false;
}

/* ---- Distribuição teórica ---- */

/** P(X = k) para X ~ Binomial(R, 1/2), calculado de forma iterativa. */
function binomialPmf(R) {
  const pmf = new Array(R + 1);
  pmf[0] = Math.pow(0.5, R);
  for (let k = 0; k < R; k++) pmf[k + 1] = pmf[k] * (R - k) / (k + 1);
  return pmf;
}

/** Densidade da Normal com média mu e desvio sigma. */
function normalDensity(x, mu, sigma) {
  const z = (x - mu) / sigma;
  return Math.exp(-0.5 * z * z) / (sigma * Math.sqrt(2 * Math.PI));
}

/* =====================================================================
 *  LAYOUT / REDIMENSIONAMENTO
 * ===================================================================== */

function computeLayout() {
  const dpr = window.devicePixelRatio || 1;
  const cssW = Math.max(260, Math.floor(dom.boardWrap.clientWidth));
  const key = [cssW, state.rows, window.innerHeight, dpr].join('|');
  if (key === view.key) return false;
  view.key = key;

  const g = geometry();
  const unitsW = state.rows + 2.6;
  const unitsH = g.yMax - g.yMin;
  const maxBoardH = Math.max(380, window.innerHeight - 150);
  const scale = Math.min((cssW - 8) / unitsW, maxBoardH / unitsH);

  view.dpr = dpr;
  view.cssW = cssW;
  view.scale = scale;
  view.boardH = Math.ceil(unitsH * scale);
  view.histH = cssW < 480 ? 190 : 230;
  view.ox = cssW / 2;
  view.oy = -g.yMin * scale;

  sizeCanvas(dom.boardCanvas, cssW, view.boardH);
  sizeCanvas(dom.histCanvas, cssW, view.histH);
  sizeCanvas(staticCanvas, cssW, view.boardH, true);

  staticDirty = histDirty = true;
  return true;
}

function sizeCanvas(canvas, cssW, cssH, offscreenOnly) {
  canvas.width = Math.round(cssW * view.dpr);
  canvas.height = Math.round(cssH * view.dpr);
  if (!offscreenOnly) canvas.style.height = cssH + 'px';
}

/** Aplica a transformação "unidades de quadro -> pixels do canvas". */
function useBoardUnits(ctx) {
  const s = view.dpr * view.scale;
  ctx.setTransform(s, 0, 0, s, view.dpr * view.ox, view.dpr * view.oy);
}

/** Transformação em pixels CSS (para textos). */
function useCssPixels(ctx) {
  ctx.setTransform(view.dpr, 0, 0, view.dpr, 0, 0);
}

function clearCanvas(ctx, canvas) {
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, canvas.width, canvas.height);
}

/* =====================================================================
 *  DESENHO DO QUADRO (camada estática: fundo, funil, pinos, compartimentos)
 * ===================================================================== */

function drawStaticLayer() {
  const ctx = staticCtx;
  const g = geometry();
  const R = state.rows;
  clearCanvas(ctx, staticCanvas);
  useBoardUnits(ctx);

  // Placa de fundo
  const half = R / 2 + 0.85;
  roundedRect(ctx, -half, g.yMin + 0.05, half * 2, g.yMax - g.yMin - 0.55, 0.45);
  ctx.fillStyle = 'rgba(255,255,255,0.025)';
  ctx.fill();
  ctx.strokeStyle = 'rgba(148,163,184,0.18)';
  ctx.lineWidth = 0.04;
  ctx.stroke();

  drawFunnel(ctx);
  drawPins(ctx);
  drawBins(ctx, g);
  drawBinContents(ctx, g);
  drawBinLabels(ctx, g);
}

function roundedRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function drawFunnel(ctx) {
  const { FUNNEL_TOP_Y: top, FUNNEL_EXIT_Y: exit, FUNNEL_TOP_HALF_WIDTH: wTop, FUNNEL_EXIT_HALF_WIDTH: wExit } = CONFIG;
  ctx.beginPath();
  ctx.moveTo(-wTop, top);
  ctx.lineTo(-wExit, exit);
  ctx.moveTo(wTop, top);
  ctx.lineTo(wExit, exit);
  ctx.strokeStyle = '#7c8ba5';
  ctx.lineWidth = 0.08;
  ctx.lineCap = 'round';
  ctx.stroke();
}

function drawPins(ctx) {
  const R = state.rows;
  // Halo suave
  ctx.beginPath();
  for (let r = 0; r < R; r++) {
    for (let k = 0; k <= r; k++) {
      const x = pinX(r, k), y = pinY(r);
      ctx.moveTo(x + 0.17, y);
      ctx.arc(x, y, 0.17, 0, Math.PI * 2);
    }
  }
  ctx.fillStyle = 'rgba(148,163,184,0.14)';
  ctx.fill();

  // Pino
  ctx.beginPath();
  for (let r = 0; r < R; r++) {
    for (let k = 0; k <= r; k++) {
      const x = pinX(r, k), y = pinY(r);
      ctx.moveTo(x + CONFIG.PIN_RADIUS, y);
      ctx.arc(x, y, CONFIG.PIN_RADIUS, 0, Math.PI * 2);
    }
  }
  ctx.fillStyle = '#e2e8f0';
  ctx.fill();
  ctx.strokeStyle = '#64748b';
  ctx.lineWidth = 0.025;
  ctx.stroke();
}

/** Divisórias e piso dos compartimentos. */
function drawBins(ctx, g) {
  const R = state.rows;
  ctx.beginPath();
  for (let b = 0; b <= R + 1; b++) {
    const x = b - R / 2 - 0.5;                 // fronteira entre compartimentos
    ctx.moveTo(x, g.binTop);
    ctx.lineTo(x, g.binBottom);
  }
  ctx.moveTo(-R / 2 - 0.5, g.binBottom);
  ctx.lineTo(R / 2 + 0.5, g.binBottom);
  ctx.strokeStyle = '#64748b';
  ctx.lineWidth = CONFIG.WALL_HALF * 2;
  ctx.lineCap = 'round';
  ctx.stroke();
}

/** Bolinhas acumuladas: pilha de bolinhas (poucas) ou barras proporcionais (muitas). */
function drawBinContents(ctx, g) {
  const R = state.rows;
  const m = binMetrics();
  const floorY = g.binBottom - 0.04;

  if (m.asBalls) {
    ctx.beginPath();
    for (let b = 0; b <= R; b++) {
      const count = state.counts[b];
      if (!count) continue;
      const cx = binCenterX(b);
      const spacing = 2 * CONFIG.BALL_RADIUS;
      for (let i = 0; i < count; i++) {
        const col = i % m.cols;
        const row = Math.floor(i / m.cols);
        const x = cx + (col - (m.cols - 1) / 2) * spacing;
        const y = floorY - CONFIG.BALL_RADIUS - row * m.rowH;
        ctx.moveTo(x + CONFIG.BALL_RADIUS, y);
        ctx.arc(x, y, CONFIG.BALL_RADIUS, 0, Math.PI * 2);
      }
    }
    ctx.fillStyle = '#fbbf24';
    ctx.fill();
    return;
  }

  for (let b = 0; b <= R; b++) {
    const h = binFillHeight(b, m);
    if (h <= 0) continue;
    const x = binCenterX(b) - m.innerW / 2;
    const grad = ctx.createLinearGradient(0, floorY - h, 0, floorY);
    grad.addColorStop(0, '#fde68a');
    grad.addColorStop(1, '#f59e0b');
    ctx.fillStyle = grad;
    ctx.fillRect(x, floorY - h, m.innerW, h);
  }
}

/** Contagem numérica abaixo de cada compartimento (somente se couber). */
function drawBinLabels(ctx, g) {
  const R = state.rows;
  const digits = String(Math.max(1, state.maxCount)).length;
  let fontSize = Math.min(13, view.scale * 0.34);
  if (digits * fontSize * 0.62 > view.scale * 0.95) fontSize = (view.scale * 0.95) / (digits * 0.62);
  if (fontSize < 7) return;

  useCssPixels(ctx);
  ctx.font = `600 ${fontSize.toFixed(1)}px system-ui, sans-serif`;
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillStyle = '#cbd5e1';
  const y = view.oy + (g.binBottom + 0.38) * view.scale;
  for (let b = 0; b <= R; b++) {
    ctx.fillText(String(state.counts[b]), view.ox + binCenterX(b) * view.scale, y);
  }
}

/* =====================================================================
 *  DESENHO DAS BOLINHAS ANIMADAS (camada dinâmica)
 * ===================================================================== */

function drawBalls() {
  const ctx = boardCtx;
  const list = state.active;
  if (list.length === 0) return;
  useBoardUnits(ctx);

  // Um único caminho para todas as bolinhas -> um único fill() (muito mais rápido)
  ctx.beginPath();
  const radius = CONFIG.BALL_RADIUS;
  for (let i = 0; i < list.length; i++) {
    const b = list[i];
    ctx.moveTo(b.x + radius, b.y);
    ctx.arc(b.x, b.y, radius, 0, Math.PI * 2);
  }
  ctx.fillStyle = '#fbbf24';
  ctx.fill();
  ctx.lineWidth = 0.03;
  ctx.strokeStyle = 'rgba(120, 53, 15, 0.75)';
  ctx.stroke();
}

/* =====================================================================
 *  HISTOGRAMA + CURVA NORMAL TEÓRICA
 * ===================================================================== */

/** Escolhe um passo "redondo" (1, 2, 5 × 10^n) para as linhas de grade. */
function niceStep(rawStep) {
  const magnitude = Math.pow(10, Math.floor(Math.log10(rawStep)));
  const norm = rawStep / magnitude;
  const factor = norm <= 1 ? 1 : norm <= 2 ? 2 : norm <= 5 ? 5 : 10;
  return factor * magnitude;
}

function drawHistogram() {
  const ctx = histCtx;
  const W = view.cssW, H = view.histH;
  const R = state.rows;
  const n = state.finished;
  const padTop = 16, padBottom = 26;
  const baseY = H - padBottom;
  const plotH = baseY - padTop;

  useCssPixels(ctx);
  ctx.clearRect(0, 0, W, H);

  const pmf = binomialPmf(R);
  const mu = R / 2;
  const sigma = Math.sqrt(R) / 2;                         // desvio padrão teórico: sqrt(R * 1/2 * 1/2)
  const expectedPeak = n * Math.max.apply(null, pmf);
  const theoryOn = state.showTheory && n > 0;
  const yMax = Math.max(state.maxCount, theoryOn ? expectedPeak : 0, 5) * 1.12;
  const yOf = (v) => baseY - (v / yMax) * plotH;
  const xOfBin = (b) => view.ox + (b - R / 2) * view.scale;  // alinhado com o quadro

  // Grade e rótulos do eixo Y
  const step = niceStep(yMax / 4);
  ctx.font = '11px system-ui, sans-serif';
  ctx.textAlign = 'left';
  ctx.textBaseline = 'bottom';
  ctx.lineWidth = 1;
  for (let v = 0; v <= yMax; v += step) {
    const y = Math.round(yOf(v)) + 0.5;
    ctx.strokeStyle = v === 0 ? 'rgba(203,213,225,0.55)' : 'rgba(148,163,184,0.14)';
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(W, y);
    ctx.stroke();
    if (v > 0) {
      ctx.fillStyle = '#94a3b8';
      ctx.fillText(fmtInt.format(v), 4, y - 2);
    }
  }

  // Barras
  const barW = view.scale * 0.88;
  for (let b = 0; b <= R; b++) {
    const c = state.counts[b];
    if (!c) continue;
    const x = xOfBin(b) - barW / 2;
    const y = yOf(c);
    const grad = ctx.createLinearGradient(0, y, 0, baseY);
    grad.addColorStop(0, '#fde68a');
    grad.addColorStop(1, '#d97706');
    ctx.fillStyle = grad;
    ctx.fillRect(x, y, barW, baseY - y);
  }

  // Curva normal teórica (escalada para n bolinhas; largura de cada classe = 1)
  if (theoryOn) {
    ctx.beginPath();
    for (let x = -0.5; x <= R + 0.5001; x += 0.05) {
      const px = view.ox + (x - R / 2) * view.scale;
      const py = yOf(n * normalDensity(x, mu, sigma));
      if (x === -0.5) ctx.moveTo(px, py); else ctx.lineTo(px, py);
    }
    ctx.strokeStyle = '#22d3ee';
    ctx.lineWidth = 2.5;
    ctx.lineJoin = 'round';
    ctx.stroke();

    // Valores esperados da binomial (pontos)
    for (let b = 0; b <= R; b++) {
      ctx.beginPath();
      ctx.arc(xOfBin(b), yOf(n * pmf[b]), 3.4, 0, Math.PI * 2);
      ctx.fillStyle = '#ffffff';
      ctx.fill();
      ctx.lineWidth = 1.5;
      ctx.strokeStyle = '#0f172a';
      ctx.stroke();
    }
  }

  // Rótulos do eixo X (número do compartimento)
  ctx.fillStyle = '#94a3b8';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'top';
  const every = view.scale < 22 ? 2 : 1;
  for (let b = 0; b <= R; b += every) ctx.fillText(String(b), xOfBin(b), baseY + 6);

  histDirty = false;
}

/* =====================================================================
 *  RENDERIZAÇÃO E LOOP DE ANIMAÇÃO
 * ===================================================================== */

function render(now) {
  if (staticDirty) {
    drawStaticLayer();
    staticDirty = false;
  }
  clearCanvas(boardCtx, dom.boardCanvas);
  boardCtx.drawImage(staticCanvas, 0, 0);      // camada estática em cópia 1:1
  drawBalls();

  if (histDirty) drawHistogram();

  if (statsDirty && (now - lastStatsTime > CONFIG.STATS_REFRESH_MS || state.status !== 'running')) {
    updateStatsDisplay();
    lastStatsTime = now;
  }
}

function frame(now) {
  rafId = 0;
  const dt = Math.min(0.05, Math.max(0, (now - lastFrameTime) / 1000));  // limita saltos (aba em segundo plano)
  lastFrameTime = now;

  if (state.status === 'running') stepSimulation(dt * state.speed);
  render(now);

  // O loop só continua enquanto a simulação estiver rodando
  if (state.status === 'running') rafId = requestAnimationFrame(frame);
}

/** Garante que exista um quadro agendado (usado em qualquer mudança de estado). */
function requestFrame() {
  if (rafId) return;
  lastFrameTime = performance.now();
  rafId = requestAnimationFrame(frame);
}

/* =====================================================================
 *  CONTROLE DA SIMULAÇÃO
 * ===================================================================== */

function resetData() {
  state.counts = new Array(state.rows + 1).fill(0);
  state.maxCount = 0;
  state.active = [];
  state.released = 0;
  state.finished = 0;
  state.background = 0;
  state.spawnCredit = 0;
  staticDirty = histDirty = statsDirty = true;
}

function startSimulation() {
  resetData();
  state.totalBalls = Number(dom.ballsRange.value);
  state.status = 'running';
  syncUI();
  requestFrame();
}

function togglePause() {
  if (state.status === 'running') state.status = 'paused';
  else if (state.status === 'paused') state.status = 'running';
  else return;
  syncUI();
  requestFrame();
}

function clearSimulation() {
  resetData();
  state.status = 'idle';
  syncUI();
  requestFrame();
}

/** Muda o número de fileiras: refaz a geometria e zera os resultados. */
function applyRows(rows) {
  state.rows = rows;
  view.key = '';
  resetData();
  state.status = 'idle';
  computeLayout();
  syncUI();
  requestFrame();
}

const STATUS_LABELS = { idle: 'Parada', running: 'Executando', paused: 'Pausada', done: 'Finalizada' };

/** Sincroniza botões, controles e indicador de estado com o estado atual. */
function syncUI() {
  const status = state.status;
  const busy = status === 'running' || status === 'paused';

  dom.statusBadge.textContent = STATUS_LABELS[status];
  dom.statusBadge.dataset.state = status;

  dom.btnStart.disabled = busy;
  dom.btnPause.disabled = !busy;
  dom.btnPause.textContent = status === 'paused' ? 'Continuar' : 'Pausar';

  dom.ballsRange.disabled = busy;
  dom.rowsRange.disabled = busy;
  dom.chips.forEach((chip) => { chip.disabled = busy; });
  statsDirty = true;
}

/* =====================================================================
 *  INICIALIZAÇÃO E EVENTOS
 * ===================================================================== */

function bindEvents() {
  dom.ballsRange.addEventListener('input', () => {
    dom.ballsValue.textContent = fmtInt.format(Number(dom.ballsRange.value));
    statsDirty = true;
    requestFrame();
  });

  dom.chips.forEach((chip) => {
    chip.addEventListener('click', () => {
      dom.ballsRange.value = chip.dataset.value;
      dom.ballsRange.dispatchEvent(new Event('input'));
    });
  });

  dom.rowsRange.addEventListener('input', () => {
    const rows = Number(dom.rowsRange.value);
    dom.rowsValue.textContent = String(rows);
    applyRows(rows);
  });

  dom.speedRange.addEventListener('input', () => {
    state.speed = Number(dom.speedRange.value);
    dom.speedValue.textContent = fmtDec.format(state.speed) + '×';
  });

  dom.theoryToggle.addEventListener('change', () => {
    state.showTheory = dom.theoryToggle.checked;
    histDirty = true;
    requestFrame();
  });

  dom.btnStart.addEventListener('click', startSimulation);
  dom.btnRestart.addEventListener('click', startSimulation);
  dom.btnPause.addEventListener('click', togglePause);
  dom.btnClear.addEventListener('click', clearSimulation);

  const onResize = () => {
    if (computeLayout()) requestFrame();
  };
  if (typeof ResizeObserver !== 'undefined') new ResizeObserver(onResize).observe(dom.boardWrap);
  window.addEventListener('resize', onResize);
}

function cacheDom() {
  const ids = [
    'boardWrap', 'boardCanvas', 'histCanvas', 'statusBadge', 'ballsRange', 'ballsValue', 'rowsRange',
    'rowsValue', 'speedRange', 'speedValue', 'theoryToggle', 'btnStart', 'btnPause', 'btnRestart',
    'btnClear', 'progressBar', 'progressText', 'statTotal', 'statDone', 'statActive',
    'statBackground', 'statBins', 'statMode', 'statMean', 'statSd',
  ];
  ids.forEach((id) => { dom[id] = document.getElementById(id); });
  dom.chips = Array.prototype.slice.call(document.querySelectorAll('#presetChips .chip'));
}

function init() {
  cacheDom();
  boardCtx = dom.boardCanvas.getContext('2d');
  histCtx = dom.histCanvas.getContext('2d');
  staticCanvas = document.createElement('canvas');   // camada estática fora da tela
  staticCtx = staticCanvas.getContext('2d');

  state.rows = Number(dom.rowsRange.value);
  state.speed = Number(dom.speedRange.value);
  state.showTheory = dom.theoryToggle.checked;
  dom.ballsValue.textContent = fmtInt.format(Number(dom.ballsRange.value));
  dom.speedValue.textContent = fmtDec.format(state.speed) + '×';

  resetData();
  computeLayout();
  bindEvents();
  syncUI();
  requestFrame();
}

document.addEventListener('DOMContentLoaded', init);
