/* HTTPS previews animate the archive counts. Direct file previews retain their static figures. */
(() => {
  if (location.protocol === 'file:') {
    document.documentElement.dataset.momentsReady = '0';
    return;
  }
  const base = new URL('.', document.currentScript.src);
  const script = document.createElement('script');
  script.type = 'module';
  script.src = new URL('moments.js', base).href;
  script.onerror = () => { document.documentElement.dataset.momentsReady = '0'; };
  document.head.append(script);
  matchMedia('(prefers-reduced-motion: reduce)').addEventListener('change', event => {
    if (event.matches) for (const host of document.querySelectorAll('[data-moment="counter-rolls"]'))
      for (const animation of host.getAnimations({ subtree: true })) animation.finish();
  });
})();
