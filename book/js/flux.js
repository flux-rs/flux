window.fetch = ((originalFetch) => {
  const fluxPlayground = "https://flux.goto.ucsd.edu/play.rust-lang.org";
  return (url, options) => {
    const redirected = url.replace(
      /https:\/\/play.rust-lang.org/,
      fluxPlayground,
    );
    return originalFetch(redirected, options);
  };
})(window.fetch);
