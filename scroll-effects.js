/* Scroll effects share the browser's real scroll position, including Lenis and native touch. */
(() => {
  const progress = document.createElement('div');
  progress.className = 'reading-progress';
  progress.setAttribute('aria-hidden', 'true');
  const fill = document.createElement('span');
  fill.className = 'reading-progress__fill';
  progress.append(fill);
  document.body.prepend(progress);

  let progressFrame = 0;
  const updateProgress = () => {
    progressFrame = 0;
    const range = document.documentElement.scrollHeight - innerHeight;
    const position = range > 0 ? Math.min(1, Math.max(0, scrollY / range)) : 0;
    fill.style.transform = `scaleX(${position.toFixed(4)})`;
  };
  const requestProgress = () => {
    if (!progressFrame) progressFrame = requestAnimationFrame(updateProgress);
  };
  addEventListener('scroll', requestProgress, { passive: true });
  addEventListener('resize', requestProgress);
  addEventListener('pageshow', requestProgress);
  if (typeof ResizeObserver === 'function') new ResizeObserver(requestProgress).observe(document.body);
  requestProgress();

  if (typeof IntersectionObserver !== 'function') return;
  const motion = matchMedia('(prefers-reduced-motion: reduce)');
  const cards = [
    '.scenario-list > li',
    '.workflow-steps > li',
    '.decision-example',
    '.featured-proof-sheet',
    '.case-guide > ul > li',
    '.research-case-list > .research-case',
    '.research-task-grid > li',
    '.community-paths > li',
    '.module-showcase',
    '.access-steps > li',
    '.initiative-contact',
    '.feedback-product',
    '.legal-summary',
    '.metrics > .metric',
    '#proof-list > li',
  ].join(',');
  const active = new Map(), seenProofs = new Set();
  const proofKey = node => node.matches('#proof-list > li') ? node.querySelector('[data-proof-id]')?.dataset.proofId : null;
  const reveal = (node, delay = 0, immediate = false) => {
    observer.unobserve(node);
    const key = proofKey(node);
    if (key) seenProofs.add(key);
    node.dataset.scrollReveal = 'done';
    if (immediate || motion.matches) {
      active.get(node)?.finish();
      return;
    }
    node.dataset.scrollReveal = 'running';
    const animation = node.animate([
      { opacity: 0, translate: '0 18px' },
      { opacity: 1, translate: '0 0' },
    ], { duration: 480, delay, easing: 'ease-out', fill: 'backwards' });
    active.set(node, animation);
    const complete = () => {
      active.delete(node);
      node.dataset.scrollReveal = 'done';
    };
    animation.finished.then(complete, complete);
  };
  const observer = new IntersectionObserver(entries => {
    const groups = new Map();
    for (const { target, isIntersecting } of entries) {
      if (!isIntersecting || target.dataset.scrollReveal !== 'pending') continue;
      const index = groups.get(target.parentElement) || 0;
      groups.set(target.parentElement, index + 1);
      reveal(target, Math.min(index, 2) * 80);
    }
  }, { rootMargin: '0px 0px -64px 0px', threshold: 0 });

  const register = root => {
    const nodes = [...root.querySelectorAll(cards)];
    if (root instanceof Element && root.matches(cards)) nodes.unshift(root);
    for (const node of nodes) {
      if (node.hasAttribute('data-scroll-reveal') || motion.matches) continue;
      const key = proofKey(node);
      if (node.matches('#proof-list > li') && !key) continue;
      if (key && seenProofs.has(key)) continue;
      node.dataset.scrollReveal = 'pending';
      observer.observe(node);
    }
  };
  register(document);

  // Filtering and selecting proof records rebuilds this list; already seen records stay visible.
  const proofList = document.getElementById('proof-list');
  if (proofList) new MutationObserver(records => {
    for (const record of records) {
      for (const node of record.removedNodes) if (node instanceof Element) {
        observer.unobserve(node);
        active.get(node)?.cancel();
      }
      for (const node of record.addedNodes) if (node instanceof Element) register(node);
    }
  }).observe(proofList, { childList: true });

  document.addEventListener('focusin', event => {
    const card = event.target.closest?.('[data-scroll-reveal]');
    if (card && card.dataset.scrollReveal !== 'done') reveal(card, 0, true);
  });
  motion.addEventListener('change', event => {
    if (!event.matches) return;
    document.querySelectorAll('[data-scroll-reveal="pending"]').forEach(node => reveal(node, 0, true));
    active.forEach(animation => animation.finish());
  });
})();
