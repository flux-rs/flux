// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded affix "><a href="index.html">Introduction</a></li><li class="chapter-item expanded affix "><a href="guide/install.html">Install &amp; Run</a></li><li class="chapter-item expanded affix "><a href="about.html">About</a></li><li class="chapter-item expanded affix "><li class="part-title">Interactive Tutorial</li><li class="chapter-item expanded "><a href="tutorial/01-refinements.html"><strong aria-hidden="true">1.</strong> Refinements</a></li><li class="chapter-item expanded "><a href="tutorial/02-ownership.html"><strong aria-hidden="true">2.</strong> Ownership</a></li><li class="chapter-item expanded "><a href="tutorial/03-structs.html"><strong aria-hidden="true">3.</strong> Structs</a></li><li class="chapter-item expanded "><a href="tutorial/04-enums.html"><strong aria-hidden="true">4.</strong> Enums</a></li><li class="chapter-item expanded "><a href="tutorial/05-vectors.html"><strong aria-hidden="true">5.</strong> Opaques</a></li><li class="chapter-item expanded "><a href="tutorial/06-consts.html"><strong aria-hidden="true">6.</strong> Consts</a></li><li class="chapter-item expanded "><a href="tutorial/07-externs.html"><strong aria-hidden="true">7.</strong> Externs</a></li><li class="chapter-item expanded "><a href="tutorial/08-traits.html"><strong aria-hidden="true">8.</strong> Traits</a></li><li class="chapter-item expanded "><div><strong aria-hidden="true">9.</strong> Iteration</div></li><li class="chapter-item expanded "><a href="tutorial/11-equality.html"><strong aria-hidden="true">10.</strong> Case Study: Simple Access Control</a></li><li class="chapter-item expanded "><a href="tutorial/12-sets.html"><strong aria-hidden="true">11.</strong> Case Study: Dynamic Access Control</a></li><li class="chapter-item expanded "><a href="tutorial/13-bitvectors.html"><strong aria-hidden="true">12.</strong> Case Study: Dependent Typestates</a></li><li class="chapter-item expanded "><a href="tutorial/14-neural.html"><strong aria-hidden="true">13.</strong> Case Study: Neural Networks</a></li><li class="chapter-item expanded affix "><li class="part-title">Appendix</li><li class="chapter-item expanded "><a href="guide/specifications.html"><strong aria-hidden="true">14.</strong> Specifications</a></li><li class="chapter-item expanded "><a href="guide/develop.html"><strong aria-hidden="true">15.</strong> Developer&#39;s Guide</a></li><li class="chapter-item expanded "><a href="guide/architecture.html"><strong aria-hidden="true">16.</strong> Architecture</a></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
