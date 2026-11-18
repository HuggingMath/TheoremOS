/* Proof figures scramble once on entering the viewport, then resolve left to right.
   The HTML holds the real value; assistive technology always reads that value.
   opts: duration before the first digit resolves (480ms), stagger between figures (90ms). */
export const phone = true;

export default function (root, opts, lib) {
  const nums = root.matches('[data-count], .t-stat') ? [root] : [...root.querySelectorAll('[data-count], .t-stat')];
  if (!nums.length || lib.reduced()) return {};

  const hold = opts.duration || 480, stagger = opts.stagger ?? 90;
  const symbols = '#%&?+=';
  const built = nums.map(el => {
    const text = el.textContent.trim();
    el.setAttribute('aria-label', text);
    const label = document.createElement('span');
    label.className = 'sr-only';
    label.textContent = text;
    const visual = document.createElement('span');
    visual.className = 'mo-cr__visual';
    visual.setAttribute('aria-hidden', 'true');
    const cols = [];
    for (const ch of text) {
      const col = document.createElement('span');
      col.className = /\d/.test(ch) ? 'mo-cr__col' : 'mo-cr__ch';
      col.textContent = ch;
      visual.append(col);
      if (/\d/.test(ch)) cols.push({ col, target: ch, resolveAt: 0 });
    }
    el.classList.add('mo-cr');
    el.replaceChildren(label, visual);
    return { el, text, cols };
  });

  const motion = matchMedia('(prefers-reduced-motion: reduce)');
  let frame = 0, startedAt = 0, done = false, seen;
  const finish = () => {
    if (done) return;
    done = true;
    cancelAnimationFrame(frame);
    seen?.destroy();
    built.forEach(({ cols }) => cols.forEach(({ col, target }) => { col.textContent = target; }));
    motion.removeEventListener('change', onPreferenceChange);
    removeEventListener('pagehide', finish);
  };
  const onPreferenceChange = event => { if (event.matches) finish(); };
  const tick = now => {
    frame = 0;
    const elapsed = now - startedAt;
    let pending = false;
    built.forEach(({ cols }) => cols.forEach(({ col, target, resolveAt }) => {
      if (elapsed >= resolveAt) col.textContent = target;
      else pending = true;
    }));
    if (pending) frame = requestAnimationFrame(tick);
    else finish();
  };
  seen = lib.once(root, () => {
    if (lib.reduced()) return finish();
    let ordinal = 0;
    built.forEach(({ cols }, n) => cols.forEach(info => {
      const { col } = info;
      col.textContent = symbols[Math.floor(Math.random() * symbols.length)];
      info.resolveAt = hold + ordinal++ * 80 + n * stagger;
    }));
    startedAt = performance.now();
    tick(startedAt);
  }, { threshold: 0.4 });
  motion.addEventListener('change', onPreferenceChange);
  addEventListener('pagehide', finish);

  return {
    destroy() {
      finish();
      built.forEach(({ el, text }) => {
        el.textContent = text;
        el.classList.remove('mo-cr');
      });
    },
  };
}
