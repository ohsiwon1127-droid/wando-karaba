// 실시간 멀티플레이어 바카라 서버 (가상 포인트 전용, 실제 결제/환전 없음)
// 아이디/비밀번호 회원가입 + 로그인, 관리자 전용 충전 시스템 포함
require('dotenv').config();
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');
const express = require('express');
const http = require('http');
const bcrypt = require('bcryptjs');
const jwt = require('jsonwebtoken');
const { Server } = require('socket.io');

const PORT = process.env.PORT || 3000;
const JWT_SECRET = process.env.JWT_SECRET || crypto.randomBytes(32).toString('hex');
const ADMIN_SIGNUP_CODE = process.env.ADMIN_SIGNUP_CODE || ''; // 비워두면 관리자 가입 코드 기능 비활성화
const DATA_FILE = path.join(__dirname, 'data', 'users.json');

const BET_MS = 10000;
const REVEAL_MS = 8000;
const DECKS = 8;
const START_BALANCE = 500; // 가입 시 기본 지급 (재미용, 부족하면 관리자에게 충전 요청)
const ODDS = { player: 1, banker: 0.95, tie: 8, playerPair: 11, bankerPair: 11 };

if (!process.env.JWT_SECRET) {
  console.warn('[경고] JWT_SECRET 환경변수가 설정되지 않아 서버 재시작마다 임시 키를 사용합니다. 배포 시에는 JWT_SECRET을 반드시 지정하세요.');
}
if (!ADMIN_SIGNUP_CODE) {
  console.warn('[경고] ADMIN_SIGNUP_CODE가 설정되지 않아 관리자 계정을 만들 수 없습니다. .env를 확인하세요.');
}

// ---------- persistence (simple JSON file, fine for hobby-scale use) ----------
function loadUsers() {
  try {
    return JSON.parse(fs.readFileSync(DATA_FILE, 'utf8'));
  } catch (e) {
    return {};
  }
}
function saveUsers() {
  try {
    fs.mkdirSync(path.dirname(DATA_FILE), { recursive: true });
    fs.writeFileSync(DATA_FILE, JSON.stringify(users, null, 2));
  } catch (e) {
    console.error('저장 실패:', e.message);
  }
}

let users = loadUsers(); // usernameLower -> { username, passwordHash, balance, isAdmin, createdAt }

function findByUsername(username) {
  return users[String(username).toLowerCase()] || null;
}

// ---------- card / baccarat logic ----------
const SUITS = ['♠', '♥', '♦', '♣'];
const SUIT_COLOR = { '♠': 'black', '♣': 'black', '♥': 'red', '♦': 'red' };
const RANKS = ['A', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K'];

function cardValue(rank) {
  if (rank === 'A') return 1;
  if (['10', 'J', 'Q', 'K'].includes(rank)) return 0;
  return parseInt(rank, 10);
}
function buildShoe() {
  const cards = [];
  for (let d = 0; d < DECKS; d++) {
    for (const suit of SUITS) {
      for (const rank of RANKS) cards.push({ rank, suit, color: SUIT_COLOR[suit] });
    }
  }
  for (let i = cards.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [cards[i], cards[j]] = [cards[j], cards[i]];
  }
  return cards;
}
function total(cards) {
  return cards.reduce((sum, c) => sum + cardValue(c.rank), 0) % 10;
}
function bankerShouldDraw(bankerTotal, playerThird) {
  if (bankerTotal <= 2) return true;
  // 플레이어가 3번째 카드를 받지 않고 스탠드한 경우(자연스레 6 또는 7), 뱅커는 자기 합이 5 이하면 무조건 드로우한다.
  if (playerThird === null) return bankerTotal <= 5;
  if (bankerTotal === 3) return playerThird !== 8;
  if (bankerTotal === 4) return playerThird >= 2 && playerThird <= 7;
  if (bankerTotal === 5) return playerThird >= 4 && playerThird <= 7;
  if (bankerTotal === 6) return playerThird === 6 || playerThird === 7;
  return false;
}
function computeRound() {
  const shoe = buildShoe();
  let idx = 0;
  const p1 = shoe[idx++], b1 = shoe[idx++], p2 = shoe[idx++], b2 = shoe[idx++];
  const playerCards = [p1, p2];
  const bankerCards = [b1, b2];
  const playerPair = p1.rank === p2.rank;
  const bankerPair = b1.rank === b2.rank;
  let pTotal = total(playerCards);
  let bTotal = total(bankerCards);
  const natural = pTotal >= 8 || bTotal >= 8;
  let playerThirdVal = null;
  if (!natural) {
    if (pTotal <= 5) {
      const c = shoe[idx++];
      playerCards.push(c);
      playerThirdVal = cardValue(c.rank);
      pTotal = total(playerCards);
    }
    if (bankerShouldDraw(bTotal, playerThirdVal)) {
      const c = shoe[idx++];
      bankerCards.push(c);
      bTotal = total(bankerCards);
    }
  }
  const outcome = pTotal > bTotal ? 'player' : bTotal > pTotal ? 'banker' : 'tie';
  return { playerCards, bankerCards, pTotal, bTotal, outcome, playerPair, bankerPair, natural };
}
function settleBet(bet, round) {
  let payout = 0;
  const m = bet.main;
  if (m) {
    if (m.side === 'player') {
      if (round.outcome === 'player') payout += m.amount * 2;
      else if (round.outcome === 'tie') payout += m.amount;
    } else if (m.side === 'banker') {
      if (round.outcome === 'banker') payout += m.amount + Math.floor(m.amount * 0.95);
      else if (round.outcome === 'tie') payout += m.amount;
    } else if (m.side === 'tie') {
      if (round.outcome === 'tie') payout += m.amount * (1 + ODDS.tie);
    }
  }
  const pr = bet.pair;
  if (pr) {
    if (pr.side === 'playerPair' && round.playerPair) payout += pr.amount * (1 + ODDS.playerPair);
    if (pr.side === 'bankerPair' && round.bankerPair) payout += pr.amount * (1 + ODDS.bankerPair);
  }
  const risked = (m ? m.amount : 0) + (pr ? pr.amount : 0);
  return { payout, net: payout - risked };
}

// ---------- round state machine (single shared table) ----------
let currentRound = { id: 0, phase: 'betting', endsAt: 0, bets: new Map(), result: null };
let history = [];

function publicBetsList() {
  const list = [];
  for (const [username, bet] of currentRound.bets.entries()) {
    list.push({ username, main: bet.main, pair: bet.pair });
  }
  return list;
}
function socketIdsFor(username) {
  const set = userSockets.get(username);
  return set ? Array.from(set) : [];
}
function pushBalance(username) {
  const u = findByUsername(username);
  if (!u) return;
  for (const sid of socketIdsFor(username)) io.to(sid).emit('balance:update', { balance: u.balance });
}
function broadcastPresence() {
  io.emit('presence:update', { count: userSockets.size });
}
function broadcastBets() {
  io.emit('bets:update', { roundId: currentRound.id, bets: publicBetsList() });
}
function startBettingPhase() {
  currentRound = { id: currentRound.id + 1, phase: 'betting', endsAt: Date.now() + BET_MS, bets: new Map(), result: null };
  io.emit('round:betting', { roundId: currentRound.id, endsAt: currentRound.endsAt });
  broadcastBets();
  setTimeout(runReveal, BET_MS);
}
function runReveal() {
  const round = computeRound();
  currentRound.phase = 'reveal';
  currentRound.result = round;
  currentRound.endsAt = Date.now() + REVEAL_MS;
  history = [round.outcome, ...history].slice(0, 50);

  const settlements = {};
  for (const [username, bet] of currentRound.bets.entries()) {
    const { payout, net } = settleBet(bet, round);
    const u = findByUsername(username);
    if (u && payout > 0) u.balance += payout;
    settlements[username] = { payout, net };
  }
  if (currentRound.bets.size > 0) saveUsers();

  io.emit('round:reveal', { roundId: currentRound.id, endsAt: currentRound.endsAt, round, history });

  for (const [username, s] of Object.entries(settlements)) {
    const u = findByUsername(username);
    for (const sid of socketIdsFor(username)) {
      io.to(sid).emit('settle', { roundId: currentRound.id, ...s, balance: u ? u.balance : 0 });
    }
  }
  setTimeout(startBettingPhase, REVEAL_MS);
}

// ---------- auth helpers ----------
const USERNAME_RE = /^[a-zA-Z0-9_]{3,16}$/;

function signToken(user) {
  return jwt.sign({ u: user.username }, JWT_SECRET, { expiresIn: '30d' });
}
function verifyToken(token) {
  try {
    const payload = jwt.verify(token, JWT_SECRET);
    return findByUsername(payload.u);
  } catch (e) {
    return null;
  }
}
function requireAuth(req, res, next) {
  const header = req.headers.authorization || '';
  const token = header.startsWith('Bearer ') ? header.slice(7) : null;
  const user = token ? verifyToken(token) : null;
  if (!user) return res.status(401).json({ error: '로그인이 필요합니다.' });
  req.user = user;
  next();
}
function requireAdmin(req, res, next) {
  if (!req.user || !req.user.isAdmin) return res.status(403).json({ error: '관리자 권한이 필요합니다.' });
  next();
}

// ---------- express app ----------
const app = express();
app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

app.get('/', (req, res) => res.redirect('/login.html'));


app.post('/api/signup', async (req, res) => {
  const { username, password, adminCode } = req.body || {};
  if (!USERNAME_RE.test(username || '')) {
    return res.status(400).json({ error: '아이디는 영문/숫자/밑줄 3~16자여야 합니다.' });
  }
  if (!password || password.length < 4) {
    return res.status(400).json({ error: '비밀번호는 4자 이상이어야 합니다.' });
  }
  if (findByUsername(username)) {
    return res.status(409).json({ error: '이미 사용 중인 아이디입니다.' });
  }
  const passwordHash = await bcrypt.hash(password, 10);
  const isAdmin = !!(ADMIN_SIGNUP_CODE && adminCode && adminCode === ADMIN_SIGNUP_CODE);
  const user = { username, passwordHash, balance: START_BALANCE, isAdmin, createdAt: Date.now() };
  users[username.toLowerCase()] = user;
  saveUsers();
  const token = signToken(user);
  res.json({ token, username: user.username, isAdmin: user.isAdmin, balance: user.balance });
});

app.post('/api/login', async (req, res) => {
  const { username, password } = req.body || {};
  const user = findByUsername(username || '');
  if (!user) return res.status(401).json({ error: '아이디 또는 비밀번호가 올바르지 않습니다.' });
  const ok = await bcrypt.compare(password || '', user.passwordHash);
  if (!ok) return res.status(401).json({ error: '아이디 또는 비밀번호가 올바르지 않습니다.' });
  const token = signToken(user);
  res.json({ token, username: user.username, isAdmin: user.isAdmin, balance: user.balance });
});

app.get('/api/me', requireAuth, (req, res) => {
  res.json({ username: req.user.username, isAdmin: req.user.isAdmin, balance: req.user.balance });
});

app.get('/api/admin/users', requireAuth, requireAdmin, (req, res) => {
  const list = Object.values(users).map(u => ({
    username: u.username, balance: u.balance, isAdmin: u.isAdmin, createdAt: u.createdAt,
  })).sort((a, b) => a.username.localeCompare(b.username));
  res.json({ users: list });
});

app.post('/api/admin/recharge', requireAuth, requireAdmin, (req, res) => {
  const { username, amount } = req.body || {};
  const target = findByUsername(username || '');
  const amt = Math.floor(Number(amount));
  if (!target) return res.status(404).json({ error: '해당 유저를 찾을 수 없습니다.' });
  if (!Number.isFinite(amt) || amt <= 0 || amt > 1000000) {
    return res.status(400).json({ error: '충전 금액이 올바르지 않습니다. (1 ~ 1,000,000)' });
  }
  target.balance += amt;
  saveUsers();
  pushBalance(target.username);
  res.json({ username: target.username, balance: target.balance });
});

const server = http.createServer(app);
const io = new Server(server);

const userSockets = new Map(); // username -> Set<socketId>

io.use((socket, next) => {
  const token = socket.handshake.auth && socket.handshake.auth.token;
  const user = token ? verifyToken(token) : null;
  if (!user) return next(new Error('인증 실패'));
  socket.data.username = user.username;
  next();
});

io.on('connection', (socket) => {
  const username = socket.data.username;
  if (!userSockets.has(username)) userSockets.set(username, new Set());
  userSockets.get(username).add(socket.id);

  const u = findByUsername(username);
  socket.emit('joined', {
    username,
    balance: u ? u.balance : 0,
    isAdmin: u ? u.isAdmin : false,
    round: { id: currentRound.id, phase: currentRound.phase, endsAt: currentRound.endsAt, result: currentRound.result },
    history,
    myBet: currentRound.bets.get(username) || null,
    bets: publicBetsList(),
  });
  broadcastPresence();

  socket.on('placeBet', ({ main, pair }) => {
    if (currentRound.phase !== 'betting') return;
    if (currentRound.bets.has(username)) return; // 라운드당 1회
    if (!main || !main.side || !(main.amount > 0)) return;
    if (!['player', 'banker', 'tie'].includes(main.side)) return;

    let pairBet = null;
    if (pair && pair.side && pair.side !== 'none') {
      if (!['playerPair', 'bankerPair'].includes(pair.side)) return;
      if (!(pair.amount > 0)) return;
      pairBet = { side: pair.side, amount: Math.floor(pair.amount) };
    }
    const mainBet = { side: main.side, amount: Math.floor(main.amount) };
    const totalStake = mainBet.amount + (pairBet ? pairBet.amount : 0);

    const target = findByUsername(username);
    if (!target || target.balance < totalStake) {
      socket.emit('errorMsg', { message: '포인트가 부족합니다. 관리자에게 충전을 요청하세요.' });
      return;
    }
    target.balance -= totalStake;
    currentRound.bets.set(username, { main: mainBet, pair: pairBet });
    saveUsers();

    pushBalance(username);
    broadcastBets();
  });

  socket.on('disconnect', () => {
    const set = userSockets.get(username);
    if (set) {
      set.delete(socket.id);
      if (set.size === 0) userSockets.delete(username);
    }
    broadcastPresence();
  });
});

// kick off the very first round
startBettingPhase();

server.listen(PORT, () => {
  console.log(`바카라 라이브 테이블 서버 실행 중: http://localhost:${PORT}`);
});

// 배포 플랫폼이 재배포/재시작 시 보내는 종료 신호를 받으면 마지막으로 한 번 더 저장한다.
// (원래 코드에는 없어서, 라운드 중간에 재시작되면 방금 반영된 잔액이 파일에 못 쓰이고 날아갈 수 있었음)
function shutdown(signal) {
  console.log(`[${signal}] 종료 신호 수신, 유저 데이터 저장 후 종료합니다...`);
  try { saveUsers(); } catch (e) { console.error('종료 전 저장 실패:', e.message); }
  process.exit(0);
}
process.on('SIGINT', () => shutdown('SIGINT'));
process.on('SIGTERM', () => shutdown('SIGTERM'));
