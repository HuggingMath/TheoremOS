/* ScrollTrigger shares the GSAP core bundled in landing.js. */
(() => {
  const hero = document.querySelector('.hero');
  const { gsap, ScrollTrigger } = window;
  if (!hero || !gsap || !ScrollTrigger) return;

  gsap.registerPlugin(ScrollTrigger);
  const story = hero.querySelector('[data-proof-story]');
  const storyFrame = story?.querySelector('[data-proof-story-frame]');
  // Pin spacing belongs to the story; keep the introduction's parallax range unchanged.
  const heroHeight = () => hero.offsetHeight - (story ? Math.max(0, story.offsetHeight - storyFrame.offsetHeight) : 0);
  const media = gsap.matchMedia();
  media.add({
    small: '(max-width: 767px)',
    motion: '(prefers-reduced-motion: no-preference)',
  }, context => {
    if (!context.conditions.motion) return;
    const strength = context.conditions.small ? 0.55 : 1;
    const timeline = gsap.timeline({
      defaults: { duration: 1, ease: 'none' },
      scrollTrigger: {
        id: 'hero-parallax',
        trigger: hero,
        start: 0,
        end: heroHeight,
        scrub: true,
        invalidateOnRefresh: true,
      },
    });

    // Background drifts slowly; the copy and proof move at separate foreground speeds.
    const layers = [
      ['.hero-parallax-background', 0.24, 280],
      ['.hero-parallax-title', -0.12, 144],
      ['.hero-parallax-media', -0.055, 64],
    ];
    for (const [selector, rate, limit] of layers) {
      const layer = hero.querySelector(selector);
      if (!layer) continue;
      // The story's frame needs untransformed ancestors to stay fixed in the viewport.
      if (layer === story) continue;
      timeline.fromTo(layer, { y: 0 }, {
        y: () => Math.sign(rate) * Math.min(heroHeight() * Math.abs(rate), limit) * strength,
        force3D: true,
      }, 0);
    }

    // The mobile replay can change height when a different checkpoint is selected.
    const observer = new ResizeObserver(() => ScrollTrigger.refresh(true));
    observer.observe(hero.querySelector('.hero-parallax-title'));
    if (storyFrame) observer.observe(storyFrame);
    else observer.observe(hero);
    return () => observer.disconnect();
  });

  document.fonts.ready.then(() => ScrollTrigger.refresh());
  addEventListener('pageshow', () => ScrollTrigger.refresh());
})();
