// 마니또 암호 도구 — 브라우저 보안 연결(https) 없이도 동작하도록 순수 JS로 작성. 생성 스크립트(node)도 같은 파일을 쓴다.
globalThis.MC = (() => {
  const P = []; for (let n = 2; P.length < 64; n++) if (P.every(p => n % p)) P.push(n);
  const frac = x => (x - Math.floor(x)) * 4294967296 >>> 0;
  const K = P.map(p => frac(Math.cbrt(p))), H0 = P.slice(0, 8).map(p => frac(Math.sqrt(p)));
  const ror = (x, n) => x >>> n | x << (32 - n);
  function sha256(m) {
    if (typeof m === "string") m = new TextEncoder().encode(m);
    const l = m.length, n = ((l + 9 + 63) >> 6) << 6, b = new Uint8Array(n), dv = new DataView(b.buffer), w = new Uint32Array(64);
    b.set(m); b[l] = 0x80; dv.setUint32(n - 4, l * 8); dv.setUint32(n - 8, Math.floor(l / 0x20000000));
    const H = H0.slice();
    for (let o = 0; o < n; o += 64) {
      for (let i = 0; i < 16; i++) w[i] = dv.getUint32(o + i * 4);
      for (let i = 16; i < 64; i++) {
        const a = w[i - 15], c = w[i - 2];
        w[i] = w[i - 16] + (ror(a, 7) ^ ror(a, 18) ^ a >>> 3) + w[i - 7] + (ror(c, 17) ^ ror(c, 19) ^ c >>> 10) | 0;
      }
      let [a, b2, c, d, e, f, g, h] = H;
      for (let i = 0; i < 64; i++) {
        const t1 = h + (ror(e, 6) ^ ror(e, 11) ^ ror(e, 25)) + (e & f ^ ~e & g) + K[i] + w[i] | 0;
        const t2 = (ror(a, 2) ^ ror(a, 13) ^ ror(a, 22)) + (a & b2 ^ a & c ^ b2 & c) | 0;
        h = g; g = f; f = e; e = d + t1 | 0; d = c; c = b2; b2 = a; a = t1 + t2 | 0;
      }
      [a, b2, c, d, e, f, g, h].forEach((v, i) => H[i] = H[i] + v | 0);
    }
    const out = new Uint8Array(32), od = new DataView(out.buffer);
    H.forEach((v, i) => od.setUint32(i * 4, v)); return out;
  }
  const cat = (...a) => { const r = new Uint8Array(a.reduce((s, x) => s + x.length, 0)); let o = 0; for (const x of a) { r.set(x, o); o += x.length; } return r; };
  const hex = b => [...b].map(v => v.toString(16).padStart(2, "0")).join("");
  const b64 = b => btoa(String.fromCharCode(...b));
  const unb64 = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
  // SHA-256 카운터 모드 스트림 + 8바이트 확인값 (틀린 키를 걸러냄)
  function xor(key, iv, data) {
    const out = new Uint8Array(data.length);
    for (let i = 0; i < data.length; i += 32) {
      const ks = sha256(cat(key, iv, new Uint8Array([i >> 24, i >> 16 & 255, i >> 8 & 255, i & 255])));
      for (let j = 0; j < 32 && i + j < data.length; j++) out[i + j] = data[i + j] ^ ks[j];
    }
    return out;
  }
  function seal(key, obj, iv) {
    const ct = xor(key, iv, new TextEncoder().encode(JSON.stringify(obj)));
    return b64(cat(iv, sha256(cat(key, iv, ct)).slice(0, 8), ct));
  }
  function open(key, s) {
    const r = unb64(s), iv = r.slice(0, 16), tag = r.slice(16, 24), ct = r.slice(24);
    if (hex(sha256(cat(key, iv, ct)).slice(0, 8)) !== hex(tag)) return null;
    return JSON.parse(new TextDecoder().decode(xor(key, iv, ct)));
  }
  // 비밀번호 → 키 (반복 해시로 대입 공격을 느리게)
  function pwKey(pw, salt, iter) {
    let k = sha256(cat(salt, new TextEncoder().encode(pw)));
    for (let i = 1; i < iter; i++) k = sha256(cat(k, salt));
    return k;
  }
  const norm = s => String(s).replace(/\s+/g, "").toLowerCase();
  const cred = (name, nick, year) => `${norm(name)}|${norm(nick)}|${String(year).trim()}`;
  const lookupId = (slot, c) => hex(sha256(`id|${slot}|${c}`)).slice(0, 20);
  const personKey = (slot, c) => sha256(`key|${slot}|${c}`);
  const iv16 = () => crypto.getRandomValues(new Uint8Array(16));
  // 운영진 원본 A = { p:[{name,nick,year}], M:[미션], s:{회차:[[받는사람idx, 미션idx], ...]} } → 페이지 데이터
  function build(A, adminKey, meta) {
    const slots = {};
    for (const [s, list] of Object.entries(A.s)) {
      const e = {};
      list.forEach(([t, mi], g) => {
        const p = A.p[g], c = cred(p.name, p.nick, p.year);
        e[lookupId(s, c)] = seal(personKey(s, c), { n: A.p[t].name, m: A.M[mi], k: A.k ? A.k[t] : t + 1 }, iv16());
      });
      slots[s] = { e };
    }
    return { ...meta, total: A.p.length, a: seal(adminKey, A, iv16()), slots };
  }
  // 추첨이 끝난 뒤 '내 카드 확인' 모드: 본인 정보로 본인 카드(고정 그림 k)와 운세 한 줄을 연다
  function buildReveal(A, adminKey, meta) {
    const e = {};
    A.p.forEach((p, g) => { const c = cred(p.name, p.nick, p.year); e[lookupId("reveal", c)] = seal(personKey("reveal", c), { n: p.name, k: A.k[g], f: A.F[g] }, iv16()); });
    return { ...meta, mode: "reveal", total: A.p.length, a: seal(adminKey, A, iv16()), e };
  }
  return { sha256, hex, b64, unb64, seal, open, pwKey, cred, lookupId, personKey, build, buildReveal };
})();
