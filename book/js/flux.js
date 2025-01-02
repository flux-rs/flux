window.fetch = (originalFetch => {
    const fluxPlayground = "http://goto.ucsd.edu:8091/play.rust-lang.org";
    return (url, options) => {
        const redirected = url.replace(/https:\/\/play.rust-lang.org/, fluxPlayground);
        return originalFetch(redirected, options);
    }
})(window.fetch);

