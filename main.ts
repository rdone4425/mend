// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/* ---- Section 3 / 5 helpers: file lines and three-tier matching ---- */

interface Split {
  lines: string[];
  br: string;
  final: boolean;
}
function splitFile(text: string): Split {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}
function joinFile(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}
const leadWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
};
const trimEndWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return trimEndWs(s);
  return trimWs(s);
}
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  const on = o.map((l) => normLine(l, tier));
  for (let i = 0; i + o.length <= lines.length; i += 1) {
    let ok = true;
    for (let k = 0; k < o.length; k += 1) {
      if (normLine(lines[i + k]!, tier) !== on[k]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}
function firstTier(lines: string[], o: string[], strict: boolean): { tier: number; occs: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t += 1) {
    const occs = occurrences(lines, o, t);
    if (occs.length > 0) return { tier: t, occs };
  }
  return null;
}

/** A replacement: O lines replaced by N lines; nToO[j] is the O index of a
 *  context line of N, or null for a line only N has. */
interface ReplaceSpec {
  o: string[];
  n: string[];
  nToO: (number | null)[];
}
function applyReplace(lines: string[], spec: ReplaceSpec, pos: number, tier: number): string[] {
  const out = lines.slice(0, pos);
  const f = spec.o.length > 0 ? leadWs(lines[pos]!) : '';
  const p = spec.o.length > 0 ? leadWs(spec.o[0]!) : '';
  for (let j = 0; j < spec.n.length; j += 1) {
    const oi = spec.nToO[j]!;
    if (oi !== null) out.push(lines[pos + oi]!);
    else {
      const s = spec.n[j]!;
      if (tier === 2 && s !== '' && s.trim() !== '' && s.startsWith(p)) out.push(f + s.slice(p.length));
      else out.push(s);
    }
  }
  out.push(...lines.slice(pos + spec.o.length));
  return out;
}

type OpItem = { kind: 'ctx' | 'del' | 'add'; text: string; noNl: boolean };
function specFromOps(items: OpItem[]): { spec: ReplaceSpec; lastCtxAddNoNl: boolean | null; lastAddNoNl: boolean | null } {
  const o: string[] = [];
  const n: string[] = [];
  const nToO: (number | null)[] = [];
  let lastCtxAdd: boolean | null = null;
  let lastAdd: boolean | null = null;
  for (const it of items) {
    if (it.kind === 'ctx') {
      nToO.push(o.length);
      o.push(it.text);
      n.push(it.text);
      lastCtxAdd = it.noNl;
    } else if (it.kind === 'del') {
      o.push(it.text);
    } else {
      n.push(it.text);
      nToO.push(null);
      lastCtxAdd = it.noNl;
      lastAdd = it.noNl;
    }
  }
  return { spec: { o, n, nToO }, lastCtxAddNoNl: lastCtxAdd, lastAddNoNl: lastAdd };
}
function checkSafe(p: string): void {
  if (!safe(p)) throw new Fail('unsafe', p);
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  moves: { old: string; new: string }[] = [];
  recordMove(old: string, nw: string): void {
    this.moves.push({ old, new: nw });
  }
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ---- Section 6: unified diffs ---- */

interface Hunk {
  a: number;
  items: OpItem[];
}
interface UniSection {
  oldPath: string | null | undefined;
  newPath: string | null | undefined;
  hasPaths: boolean;
  createFlag: boolean;
  deleteFlag: boolean;
  hunks: Hunk[];
}
function uniPathField(s: string): string | null {
  const raw = s.slice(4).split('\t')[0]!.trim();
  if (raw === '/dev/null') return null;
  if (raw.startsWith('a/') || raw.startsWith('b/')) return raw.slice(2);
  return raw;
}
function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let headerOpen = false;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = { oldPath: m[1], newPath: m[2], hasPaths: false, createFlag: false, deleteFlag: false, hunks: [] };
      sections.push(cur);
      headerOpen = true;
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && headerOpen && cur.hunks.length === 0) {
        cur.oldPath = uniPathField(line);
        cur.newPath = uniPathField(lines[i + 1]!);
        cur.hasPaths = true;
        headerOpen = false;
        i += 2;
        continue;
      }
      cur = { oldPath: uniPathField(line), newPath: uniPathField(lines[i + 1]!), hasPaths: true, createFlag: false, deleteFlag: false, hunks: [] };
      sections.push(cur);
      headerOpen = false;
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(?:\s.*)?$/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const a = Number(m[1]);
      const body: string[] = [];
      let j = i + 1;
      while (j < n) {
        const bl = lines[j]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          body.push(bl);
          j += 1;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      const items: OpItem[] = [];
      for (const bl of body) {
        if (bl.startsWith('\\')) {
          if (items.length > 0) items[items.length - 1]!.noNl = true;
        } else if (bl === '') items.push({ kind: 'ctx', text: '', noNl: false });
        else if (bl[0] === ' ') items.push({ kind: 'ctx', text: bl.slice(1), noNl: false });
        else if (bl[0] === '-') items.push({ kind: 'del', text: bl.slice(1), noNl: false });
        else items.push({ kind: 'add', text: bl.slice(1), noNl: false });
      }
      cur.hunks.push({ a, items });
      headerOpen = false;
      i = j;
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('rename from ')) {
        if (!cur.hasPaths) cur.oldPath = line.slice('rename from '.length).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('rename to ')) {
        if (!cur.hasPaths) cur.newPath = line.slice('rename to '.length).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.createFlag = true;
        i += 1;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.deleteFlag = true;
        i += 1;
        continue;
      }
      i += 1;
      continue;
    }
    i += 1;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  for (const sec of sections) {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    edits.push((tree) => {
      if (oldP !== undefined && oldP !== null) checkSafe(oldP);
      if (newP !== undefined && newP !== null) checkSafe(newP);
      const isCreate = sec.createFlag || oldP === null;
      const isDelete = sec.deleteFlag || newP === null;
      if (isCreate) {
        const np = newP as string;
        if (tree.get(np) !== null) throw new Fail('exists', np);
        const plus: string[] = [];
        let lastAddNoNl: boolean | null = null;
        for (const h of sec.hunks) {
          for (const it of h.items) {
            if (it.kind === 'add') {
              plus.push(it.text);
              lastAddNoNl = it.noNl;
            }
          }
        }
        const text = plus.length === 0 ? '' : plus.join('\n') + (lastAddNoNl ? '' : '\n');
        tree.now.set(np, text);
        return;
      }
      if (isDelete) {
        const op = oldP as string;
        if (tree.get(op) === null) throw new Fail('missing', op);
        tree.now.set(op, null);
        return;
      }
      const op = oldP as string;
      const np = newP as string;
      const isMove = op !== np;
      const before = tree.get(op);
      if (before === null) throw new Fail('missing', op);
      if (isMove && tree.get(np) !== null) throw new Fail('exists', np);
      const cur0 = splitFile(before);
      let curLines = cur0.lines;
      let curFinal = cur0.final;
      let d = 0;
      for (const h of sec.hunks) {
        const { spec, lastCtxAddNoNl } = specFromOps(h.items);
        if (spec.o.length === 0) {
          const pos = Math.min(Math.max(h.a + d, 0), curLines.length);
          const addLines = spec.n;
          const nl = [...curLines.slice(0, pos), ...addLines, ...curLines.slice(pos)];
          let nf = curFinal;
          if (pos === curLines.length) {
            if (lastCtxAddNoNl !== null) nf = !lastCtxAddNoNl;
          }
          curLines = nl;
          curFinal = nf;
          d += spec.n.length;
        } else {
          const found = firstTier(curLines, spec.o, strict);
          if (found === null) throw new Fail('no-match', op);
          const target = h.a - 1 + d;
          let best = found.occs[0]!;
          let bestDist = Math.abs(best - target);
          for (const oc of found.occs) {
            const dist = Math.abs(oc - target);
            if (dist < bestDist) {
              best = oc;
              bestDist = dist;
            }
          }
          const atEnd = best + spec.o.length === curLines.length;
          curLines = applyReplace(curLines, spec, best, found.tier);
          if (atEnd) {
            if (lastCtxAddNoNl !== null) curFinal = !lastCtxAddNoNl;
            else curFinal = true;
          }
          d += spec.n.length - spec.o.length;
        }
      }
      const out = joinFile(curLines, cur0.br, curFinal);
      if (isMove) {
        tree.now.set(op, null);
        tree.now.set(np, out);
        tree.recordMove(op, np);
      } else {
        tree.now.set(op, out);
      }
    });
  }
  return edits;
}

/* ---- Section 7: SEARCH/REPLACE blocks ---- */

function srEdits(lines: string[], strict: boolean): Edit[] {
  interface Block {
    path: string;
    oldLines: string[];
    newLines: string[];
  }
  const blocks: Block[] = [];
  let prevEnd = 0;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let j = searchIdx - 1; j >= prevEnd; j -= 1) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (blocks.length > 0) path = blocks[blocks.length - 1]!.path;
      else throw new Exit2(`error: parse ${searchIdx + 1}`);
    }
    let eqIdx = -1;
    for (let j = searchIdx + 1; j < n; j += 1) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      if (lines[j]!.trimEnd() === '=======') {
        eqIdx = j;
        break;
      }
    }
    let endIdx = -1;
    if (eqIdx >= 0) {
      for (let j = eqIdx + 1; j < n; j += 1) {
        if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          endIdx = j;
          break;
        }
      }
    }
    if (eqIdx < 0 || endIdx < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    blocks.push({ path, oldLines: lines.slice(searchIdx + 1, eqIdx), newLines: lines.slice(eqIdx + 1, endIdx) });
    prevEnd = endIdx + 1;
    i = endIdx + 1;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => (tree) => {
    checkSafe(b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      const text = b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n';
      tree.now.set(b.path, text);
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new Fail('missing', b.path);
    const cur = splitFile(before);
    const found = firstTier(cur.lines, b.oldLines, strict);
    if (found === null) throw new Fail('no-match', b.path);
    if (found.occs.length > 1) throw new Fail('ambiguous', b.path);
    const spec: ReplaceSpec = { o: b.oldLines, n: b.newLines, nToO: b.newLines.map(() => null) };
    const nl = applyReplace(cur.lines, spec, found.occs[0]!, found.tier);
    tree.now.set(b.path, joinFile(nl, cur.br, cur.final));
  });
}

/* ---- Section 8: V4A patches ---- */

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const n = lines.length;
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = n - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${n + 1}`);
  interface Chunk {
    anchor: string | null;
    items: OpItem[];
    eof: boolean;
  }
  interface Section {
    kind: 'add' | 'delete' | 'update';
    path: string;
    moveTo: string | null;
    lines: string[];
    chunks: Chunk[];
    updateLine: number;
  }
  const sections: Section[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i += 1;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      const fileLines: string[] = [];
      i += 1;
      while (i < last && (lines[i]!.startsWith('+') || lines[i]! === '')) {
        fileLines.push(lines[i] === '' ? '' : lines[i]!.slice(1));
        i += 1;
      }
      while (fileLines.length > 0 && fileLines[fileLines.length - 1] === '') fileLines.pop();
      sections.push({ kind: 'add', path, moveTo: null, lines: fileLines, chunks: [], updateLine: 0 });
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      sections.push({ kind: 'delete', path, moveTo: null, lines: [], chunks: [], updateLine: 0 });
      i += 1;
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice('*** Update File: '.length).trim();
      const updateLine = i + 1;
      i += 1;
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to: ')) {
        moveTo = lines[i]!.slice('*** Move to: '.length).trim();
        i += 1;
      }
      const chunks: Chunk[] = [];
      let curChunk: Chunk | null = null;
      const finishChunk = (): void => {
        if (curChunk !== null) {
          while (curChunk.items.length > 0 && curChunk.items[curChunk.items.length - 1]!.kind === 'ctx' && curChunk.items[curChunk.items.length - 1]!.text === '') curChunk.items.pop();
          // A chunk made only of blank lines (at the end of a section, which
          // are not part of it) is no chunk at all.
          if (curChunk.items.length > 0 || curChunk.anchor !== null || curChunk.eof) chunks.push(curChunk);
          curChunk = null;
        }
      };
      while (i < last) {
        const l = lines[i]!;
        if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) break;
        if (l.trim() === '*** End of File') {
          if (curChunk === null) curChunk = { anchor: null, items: [], eof: true };
          else curChunk.eof = true;
          finishChunk();
          i += 1;
          break;
        }
        if (l.startsWith('@@')) {
          finishChunk();
          curChunk = { anchor: l.slice(2).trim(), items: [], eof: false };
          i += 1;
          continue;
        }
        if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
          if (curChunk === null) curChunk = { anchor: null, items: [], eof: false };
          if (l === '') curChunk.items.push({ kind: 'ctx', text: '', noNl: false });
          else if (l[0] === ' ') curChunk.items.push({ kind: 'ctx', text: l.slice(1), noNl: false });
          else if (l[0] === '-') curChunk.items.push({ kind: 'del', text: l.slice(1), noNl: false });
          else curChunk.items.push({ kind: 'add', text: l.slice(1), noNl: false });
          i += 1;
          continue;
        }
        if (blank(l)) {
          i += 1;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      finishChunk();
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLine}`);
      sections.push({ kind: 'update', path, moveTo, lines: [], chunks, updateLine });
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((sec) => (tree) => {
    checkSafe(sec.path);
    if (sec.moveTo !== null) checkSafe(sec.moveTo);
    if (sec.kind === 'add') {
      if (tree.get(sec.path) !== null) throw new Fail('exists', sec.path);
      const text = sec.lines.length === 0 ? '' : sec.lines.join('\n') + '\n';
      tree.now.set(sec.path, text);
      return;
    }
    if (sec.kind === 'delete') {
      if (tree.get(sec.path) === null) throw new Fail('missing', sec.path);
      tree.now.set(sec.path, null);
      return;
    }
    const before = tree.get(sec.path);
    if (before === null) throw new Fail('missing', sec.path);
    if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    const cur0 = splitFile(before);
    let curLines = cur0.lines;
    let cursor = 0;
    for (const ch of sec.chunks) {
      if (ch.anchor !== null && ch.anchor !== '') {
        let foundAt = -1;
        for (let t = 0; t <= (strict ? 0 : 2); t += 1) {
          for (let k = cursor; k < curLines.length; k += 1) {
            if (normLine(curLines[k]!, t) === normLine(ch.anchor, t)) {
              foundAt = k;
              break;
            }
          }
          if (foundAt >= 0) break;
        }
        if (foundAt < 0) throw new Fail('no-match', sec.path);
        cursor = foundAt + 1;
      } else if (ch.anchor === '') {
        // empty anchor: no anchor
      }
      const { spec } = specFromOps(ch.items);
      if (spec.o.length === 0) {
        const pos = ch.eof ? curLines.length : cursor;
        const nl = [...curLines.slice(0, pos), ...spec.n, ...curLines.slice(pos)];
        curLines = nl;
        cursor = pos + spec.n.length;
      } else {
        // first tier with an occurrence at or after cursor (and, for eof, ending at last line)
        let chosen: { tier: number; pos: number } | null = null;
        const maxT = strict ? 0 : 2;
        for (let t = 0; t <= maxT && chosen === null; t += 1) {
          for (const oc of occurrences(curLines, spec.o, t)) {
            if (oc < cursor) continue;
            if (ch.eof && oc + spec.o.length !== curLines.length) continue;
            chosen = { tier: t, pos: oc };
            break;
          }
        }
        if (chosen === null) throw new Fail('no-match', sec.path);
        curLines = applyReplace(curLines, spec, chosen.pos, chosen.tier);
        cursor = chosen.pos + spec.n.length;
      }
    }
    const out = joinFile(curLines, cur0.br, cur0.final);
    if (sec.moveTo !== null) {
      tree.now.set(sec.path, null);
      tree.now.set(sec.moveTo, out);
      tree.recordMove(sec.path, sec.moveTo);
    } else {
      tree.now.set(sec.path, out);
    }
  });
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? srEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const beforeMoves = [...tree.moves];
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves = beforeMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // Output rows: R lines replace a D+A pair for a qualifying move, sorted by <new>.
  const qualified = tree.moves.filter(
    (m) => tree.original(m.old) !== null && tree.get(m.old) === null && tree.original(m.new) === null && tree.get(m.new) !== null,
  );
  const covered = new Set<string>();
  for (const m of qualified) {
    covered.add(m.old);
    covered.add(m.new);
  }
  const rowObjs: { key: string; text: string }[] = [];
  for (const p of [...tree.now.keys()]) {
    if (covered.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rowObjs.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const m of qualified) rowObjs.push({ key: m.new, text: `R ${m.old} -> ${m.new}` });
  rowObjs.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const rows = rowObjs.map((r) => r.text);
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
