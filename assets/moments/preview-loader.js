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
})();
