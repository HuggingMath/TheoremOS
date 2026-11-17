// Replay saved TriangleFace checkpoints; this preview never starts a research run.
(() => {
  const stage = document.querySelector('[data-hero-proof]');
  if (!stage) return;

  const entries = [...stage.querySelectorAll('[data-proof-entry]')];
  const panels = [...stage.querySelectorAll('[data-proof-panel]')];
  const choices = [...stage.querySelectorAll('[data-proof-select]')];
  const play = stage.querySelector('[data-proof-play]');
  const restart = stage.querySelector('[data-proof-restart]');
  const position = stage.querySelector('[data-proof-position]');
  const receipt = stage.querySelector('[data-proof-receipt]');
  const motion = window.matchMedia('(prefers-reduced-motion: reduce)');
  const total = panels.length;
  let current = total;
  let playing = false;
  let started = motion.matches;
  let inView = false;
  let timer = 0;

  function stopTimer() {
    window.clearTimeout(timer);
    timer = 0;
  }

  function render() {
    stage.dataset.proofCurrent = String(current);
    stage.dataset.proofPlaying = String(playing);
    entries.forEach(node => {
      const step = Number(node.dataset.proofEntry);
      node.hidden = step > current;
      node.classList.toggle('is-current', step === current);
    });
    panels.forEach(node => { node.hidden = Number(node.dataset.proofPanel) !== current; });
    choices.forEach(button => {
      button.setAttribute('aria-pressed', String(Number(button.dataset.proofSelect) === current));
    });
    position.textContent = `${String(current).padStart(2, '0')} / ${String(total).padStart(2, '0')}`;
    receipt.textContent = current === total ? '完整原题 · 本地验收通过' : `已展示 ${current} / ${total} 个检查节点`;
    play.textContent = playing ? '暂停' : current === total ? '播放' : '继续';
    play.setAttribute('aria-pressed', String(playing));
    play.setAttribute('aria-label', playing ? '暂停解题动画' : '播放解题动画');
  }

  function schedule() {
    stopTimer();
    if (!playing || !inView || document.hidden) return;
    timer = window.setTimeout(() => {
      current += 1;
      if (current >= total) playing = false;
      render();
      schedule();
    }, 2400);
  }

  function start() {
    started = true;
    if (current === total) current = 1;
    playing = true;
    render();
    schedule();
  }

  play.addEventListener('click', () => {
    if (!playing) return start();
    playing = false;
    stopTimer();
    render();
  });
  restart.addEventListener('click', () => {
    current = total;
    start();
  });
  choices.forEach(button => {
    button.disabled = false;
    button.addEventListener('click', () => {
      started = true;
      playing = false;
      current = Number(button.dataset.proofSelect);
      stopTimer();
      render();
    });
  });
  motion.addEventListener('change', () => {
    if (!motion.matches) return;
    started = true;
    playing = false;
    current = total;
    stopTimer();
    render();
  });
  document.addEventListener('visibilitychange', schedule);
  window.addEventListener('pagehide', stopTimer);
  window.addEventListener('pageshow', schedule);

  stage.querySelector('.hero-proof-controls').hidden = false;
  render();
  stage.dataset.proofReady = 'true';
  if ('IntersectionObserver' in window) {
    new IntersectionObserver(([entry]) => {
      inView = entry.isIntersecting && entry.intersectionRatio >= 0.2;
      if (inView && !started && !motion.matches) start();
      else schedule();
    }, { threshold: 0.2 }).observe(stage);
  } else {
    inView = true;
    if (!started && !motion.matches) start();
  }
})();
