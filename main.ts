import { readdirSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';

function solve(text) {
  const lines = text.split('\n').filter(Boolean), width = Math.max(...lines.map(s => s.length));
  const size = width * lines.length, wall = new Uint8Array(size).fill(1), boxes = [], goals = [];
  let player = -1;
  lines.forEach((line, y) => [...line].forEach((c, x) => {
    const p = y * width + x;
    if (c !== '#') wall[p] = 0;
    if ('.*+'.includes(c)) goals.push(p);
    if ('$*'.includes(c)) boxes.push(p);
    if ('@+'.includes(c)) player = p;
  }));
  const dirs = [-width, width, -1, 1], moves = 'udlr';
  // Reverse-push distances account for the player's required standing square.
  function distances(goal, walls) {
    const d = new Int16Array(size).fill(-1), queue = [goal]; d[goal] = 0;
    for (let i = 0; i < queue.length; i++) for (const step of dirs) {
      const p = queue[i] - step, behind = p - step;
      if (p >= 0 && behind >= 0 && p < size && behind < size && !walls[p] && !walls[behind] && d[p] < 0) {
        d[p] = d[queue[i]] + 1; queue.push(p);
      }
    }
    return d;
  }
  const globalDistances = goals.map(g => distances(g, wall));
  const cut = new Uint8Array(size), row = Math.floor(player / width);
  for (let p = row * width; p < (row + 1) * width; p++)
    if (!wall[p] && globalDistances.every(d => d[p] < 0)) cut[p] = 1;
  const part = new Int16Array(size).fill(-1), rooms = [];
  for (let p = 0; p < size; p++) if (!wall[p] && !cut[p] && part[p] < 0) {
    const id = rooms.length, queue = [p]; part[p] = id;
    for (let i = 0; i < queue.length; i++) for (const d of dirs) {
      const q = queue[i] + d;
      if (q >= 0 && q < size && !wall[q] && !cut[q] && part[q] < 0) { part[q] = id; queue.push(q); }
    }
    rooms.push({ boxes: [], goals: [], done: false });
  }
  for (const b of boxes) if (part[b] >= 0) rooms[part[b]].boxes.push(b);
  for (const g of goals) if (part[g] >= 0) rooms[part[g]].goals.push(g);
  const active = rooms.filter(r => r.boxes.length);
  if (boxes.some(b => part[b] < 0) || goals.some(g => part[g] < 0) || rooms.some(r => r.boxes.length !== r.goals.length)) return '';
  // An initial player inside a room must be able to leave before its boxes become walls.
  const startingRoom = rooms[part[player]], firstRoom = active.indexOf(startingRoom);
  if (firstRoom > 0) active.unshift(active.splice(firstRoom, 1)[0]);
  let answer = '';
  for (const room of active) {
    const walls = wall.slice(), occupied = new Uint8Array(size), isGoal = new Uint8Array(size);
    for (const other of active) if (other !== room) for (const b of other.done ? other.goals : other.boxes) walls[b] = 1;
    for (const g of room.goals) isGoal[g] = 1;
    const dist = room.goals.map(g => distances(g, walls));
    function estimate(bs) {
      let best = 9999;
      function assign(i, used, sum) {
        if (sum >= best) return;
        if (i === bs.length) { best = sum; return; }
        for (let j = 0; j < dist.length; j++) if (!(used & (1 << j)) && dist[j][bs[i]] >= 0)
          assign(i + 1, used | (1 << j), sum + dist[j][bs[i]]);
      }
      assign(0, 0, 0); return best;
    }
    function reachable(start) {
      const seen = new Uint8Array(size), queue = [start]; seen[start] = 1; let low = start;
      for (let i = 0; i < queue.length; i++) {
        const p = queue[i]; if (p < low) low = p;
        for (const d of dirs) { const q = p + d; if (q >= 0 && q < size && !walls[q] && !occupied[q] && !seen[q]) { seen[q] = 1; queue.push(q); } }
      }
      return [seen, low];
    }
    function blocked(p) {
      for (const a of [p, p - 1, p - width, p - width - 1]) {
        const square = [a, a + 1, a + width, a + width + 1];
        if (square.every(q => walls[q] || occupied[q]) && square.some(q => occupied[q] && !isGoal[q])) return true;
      }
      return false;
    }
    const heap = [];
    function push(s) {
      let i = heap.length; heap.push(s);
      while (i) { const p = (i - 1) >> 1; if (heap[p].f <= s.f) break; heap[i] = heap[p]; i = p; }
      heap[i] = s;
    }
    function pop() {
      const top = heap[0], last = heap.pop();
      if (heap.length) { let i = 0; while (i * 2 + 1 < heap.length) {
        let j = i * 2 + 1; if (j + 1 < heap.length && heap[j + 1].f < heap[j].f) j++;
        if (heap[j].f >= last.f) break; heap[i] = heap[j]; i = j;
      } heap[i] = last; }
      return top;
    }
    const start = room.boxes.slice().sort((a, b) => a - b);
    const key = (bs, low) => bs.join(',') + ':' + low;
    for (const b of start) occupied[b] = 1;
    const startRegion = reachable(player)[1];
    for (const b of start) occupied[b] = 0;
    let solution = null;
    for (const weight of [1, 3]) {
      heap.length = 0;
      const best = new Map(), first = { boxes: start, player, cost: 0, f: weight * estimate(start), parent: null };
      best.set(key(start, startRegion), 0); push(first);
      let expanded = 0;
      while (heap.length && expanded++ < 250000) {
        const state = pop();
        for (const b of state.boxes) occupied[b] = 1;
        const [seen, low] = reachable(state.player);
        if (best.get(key(state.boxes, low)) !== state.cost) { for (const b of state.boxes) occupied[b] = 0; continue; }
        if (state.boxes.every(b => isGoal[b])) { solution = state; for (const b of state.boxes) occupied[b] = 0; break; }
        for (let i = 0; i < state.boxes.length; i++) for (let k = 0; k < 4; k++) {
          const from = state.boxes[i], to = from + dirs[k];
          if (!seen[from - dirs[k]] || walls[to] || occupied[to]) continue;
          occupied[from] = 0; occupied[to] = 1;
          if (!blocked(to)) {
            const next = state.boxes.slice(); next[i] = to; next.sort((a, b) => a - b);
            const h = estimate(next);
            if (h < 9999) {
              const region = reachable(from)[1], id = key(next, region), cost = state.cost + 1;
              if (!best.has(id) || best.get(id) > cost) {
                best.set(id, cost); push({ boxes: next, player: from, cost, f: cost + weight * h, parent: state, from, direction: k });
              }
            }
          }
          occupied[to] = 0; occupied[from] = 1;
        }
        for (const b of state.boxes) occupied[b] = 0;
      }
      if (solution) break;
    }
    if (!solution) return '';
    const pushes = [];
    for (let s = solution; s.parent; s = s.parent) pushes.push(s);
    pushes.reverse(); let current = start;
    for (const s of pushes) {
      for (const b of current) occupied[b] = 1;
      const target = s.from - dirs[s.direction], previous = new Int32Array(size).fill(-1), how = new Int8Array(size), queue = [player];
      previous[player] = player;
      for (let i = 0; i < queue.length && previous[target] < 0; i++) for (let k = 0; k < 4; k++) {
        const q = queue[i] + dirs[k];
        if (q >= 0 && q < size && !walls[q] && !occupied[q] && previous[q] < 0) { previous[q] = queue[i]; how[q] = k; queue.push(q); }
      }
      if (previous[target] < 0) return '';
      let walk = ''; for (let p = target; p !== player; p = previous[p]) walk = moves[how[p]] + walk;
      answer += walk + moves[s.direction]; player = s.from;
      for (const b of current) occupied[b] = 0;
      current = s.boxes;
    }
    room.done = true;
  }
  return answer.length <= 65536 ? answer : '';
}

const input = process.env.MAKEFUN_INPUT_DIR ?? '/input', output = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(input).sort()) {
  let result = '';
  try { result = solve(readFileSync(join(input, id, 'level.txt'), 'utf8')); } catch {}
  mkdirSync(join(output, id), { recursive: true });
  writeFileSync(join(output, id, 'solution.txt'), result);
}
