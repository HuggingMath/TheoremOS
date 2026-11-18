/* Shared scroll enhancement. Lenis 1.3.27 is served locally under its MIT license. */
(() => {
  if (typeof window.Lenis !== 'function') return;

  const motion = matchMedia('(prefers-reduced-motion: reduce)');
  const scroll = new Lenis({
    autoRaf: true,
    lerp: 0.14,
    smoothWheel: true,
    syncTouch: false,
    autoToggle: true,
    allowNestedScroll: true,
    naiveDimensions: true,
    stopInertiaOnNavigate: true,
    virtualScroll: () => !motion.matches,
  });

  // Handle section links separately from the archive's hash-based application routes.
  document.addEventListener('click', event => {
    if (event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const link = event.target.closest?.('a[href]');
    if (!link || link.hasAttribute('download') || (link.target && link.target !== '_self') || link.classList.contains('skip-link')) return;
    const destination = new URL(link.href);
    if (destination.origin !== location.origin || destination.pathname !== location.pathname || destination.search !== location.search || !destination.hash) return;
    const target = document.getElementById(decodeURIComponent(destination.hash.slice(1)));
    if (!target) return;

    event.preventDefault();
    const oldURL = location.href;
    if (destination.href !== oldURL) {
      history.pushState(null, '', destination.href);
      dispatchEvent(new HashChangeEvent('hashchange', { oldURL, newURL: destination.href }));
    }
    if (!target.hasAttribute('tabindex')) target.setAttribute('tabindex', '-1');
    target.focus({ preventScroll: true });
    scroll.scrollTo(target, { duration: 0.65 });
  });

  // Direct interaction takes over immediately, even during wheel inertia.
  document.addEventListener('pointerdown', () => scroll.reset(), { passive: true });
  document.addEventListener('keydown', event => {
    if (['Tab', 'ArrowUp', 'ArrowDown', 'PageUp', 'PageDown', 'Home', 'End', ' '].includes(event.key)) scroll.reset();
  }, { capture: true });

  motion.addEventListener('change', event => { if (event.matches) scroll.reset(); });
  addEventListener('popstate', () => scroll.reset());
  addEventListener('pagehide', () => scroll.reset());
  addEventListener('pageshow', () => { scroll.resize(); scroll.reset(); });
})();
