// // slides.js - Adds slide functionality to mdbook
// document.addEventListener('DOMContentLoaded', function () {
//     // Configuration
//     const slideDelimiter = "<!-- SLIDE -->";
//     const slideClassName = "slides";
//     const slidesContainerId = "slides-container";

//     // Get the main content container
//     const contentContainer = document.querySelector('.content');
//     if (!contentContainer) return;

//     // Get the content's HTML
//     let contentHtml = contentContainer.innerHTML;

//     // Check if this page contains slides
//     if (!contentHtml.includes(slideDelimiter)) return;

//     // Split content by slide delimiter
//     let slideContents = contentHtml.split(slideDelimiter);

//     // Create slides container
//     const slidesContainer = document.createElement('div');
//     slidesContainer.id = slidesContainerId;

//     // Create navigation controls
//     const navControls = document.createElement('div');
//     navControls.className = 'nav-controls';
//     navControls.innerHTML = `
//         <button id="prevBtn" class="nav-btn">← Previous</button>
//         <div class="slide-counter">Slide <span id="currentSlide">1</span> of <span id="totalSlides">${slideContents.length}</span></div>
//         <button id="nextBtn" class="nav-btn">Next →</button>
//     `;

//     // Add navigation to container
//     slidesContainer.appendChild(navControls);

//     // Create and add slides
//     let currentSlideIndex = 0;
//     slideContents.forEach((content, index) => {
//         const slide = document.createElement('div');
//         slide.className = slideClassName;
//         slide.innerHTML = content.trim();

//         // Make the first slide visible
//         if (index === 0) {
//             slide.classList.add('active-slide');
//         }

//         slidesContainer.appendChild(slide);
//     });

//     // Replace original content with slides
//     contentContainer.innerHTML = '';
//     contentContainer.appendChild(slidesContainer);

//     // Get slide elements
//     const slides = document.querySelectorAll(`.${slideClassName}`);
//     const prevBtn = document.getElementById('prevBtn');
//     const nextBtn = document.getElementById('nextBtn');
//     const currentSlideSpan = document.getElementById('currentSlide');

//     // Update navigation button states
//     function updateNavButtons() {
//         prevBtn.disabled = currentSlideIndex === 0;
//         nextBtn.disabled = currentSlideIndex === slides.length - 1;
//     }

//     // Move to previous slide
//     function goToPrevSlide() {
//         if (currentSlideIndex > 0) {
//             slides[currentSlideIndex].classList.remove('active-slide');
//             currentSlideIndex--;
//             slides[currentSlideIndex].classList.add('active-slide');
//             currentSlideSpan.textContent = currentSlideIndex + 1;
//             updateNavButtons();
//         }
//     }

//     // Move to next slide
//     function goToNextSlide() {
//         if (currentSlideIndex < slides.length - 1) {
//             slides[currentSlideIndex].classList.remove('active-slide');
//             currentSlideIndex++;
//             slides[currentSlideIndex].classList.add('active-slide');
//             currentSlideSpan.textContent = currentSlideIndex + 1;
//             updateNavButtons();
//         }
//     }

//     // Add event listeners
//     prevBtn.addEventListener('click', goToPrevSlide);
//     nextBtn.addEventListener('click', goToNextSlide);

//     // Add keyboard navigation
//     document.addEventListener('keydown', function (e) {
//         if (e.key === 'ArrowLeft') {
//             goToPrevSlide();
//         } else if (e.key === 'ArrowRight') {
//             goToNextSlide();
//         }
//     });

//     // Initialize buttons
//     updateNavButtons();
// });




// slides.js - Modified to work with existing slide divs
document.addEventListener('DOMContentLoaded', function () {
    // Configuration
    const slideClassName = "slides";

    // Get the main content container
    // const contentContainer = document.querySelector('.content');
    const contentContainer = document.querySelector('main');
    if (!contentContainer) return;

    // Find all existing slide divs
    const slides = contentContainer.querySelectorAll(`.${slideClassName}`);

    // Check if this page contains slides
    if (!slides || slides.length === 0) return;

    // Create navigation controls
    const navControls = document.createElement('div');
    navControls.className = 'nav-controls';
    navControls.innerHTML = `
        <button id="prevBtn" class="nav-btn">←</button>
        <div class="slide-counter">Slide <span id="currentSlide">1</span> of <span id="totalSlides">${slides.length}</span></div>
        <button id="nextBtn" class="nav-btn">→</button>
    `;


    // Add navigation to the beginning of content container
    contentContainer.insertBefore(navControls, contentContainer.firstChild);

    // Initialize slide visibility - show first, hide rest
    let currentSlideIndex = 0;
    slides.forEach((slide, index) => {
        if (index === 0) {
            slide.style.display = 'block';
        } else {
            slide.style.display = 'none';
        }
    });

    // Get navigation elements
    const prevBtn = document.getElementById('prevBtn');
    const nextBtn = document.getElementById('nextBtn');
    const currentSlideSpan = document.getElementById('currentSlide');

    // Update navigation button states
    function updateNavButtons() {
        prevBtn.disabled = currentSlideIndex === 0;
        nextBtn.disabled = currentSlideIndex === slides.length - 1;
    }

    // Move to previous slide
    function goToPrevSlide() {
        if (currentSlideIndex > 0) {
            slides[currentSlideIndex].style.display = 'none';
            currentSlideIndex--;
            slides[currentSlideIndex].style.display = 'block';
            currentSlideSpan.textContent = currentSlideIndex + 1;
            updateNavButtons();
        }
    }

    // Move to next slide
    function goToNextSlide() {
        if (currentSlideIndex < slides.length - 1) {
            slides[currentSlideIndex].style.display = 'none';
            currentSlideIndex++;
            slides[currentSlideIndex].style.display = 'block';
            currentSlideSpan.textContent = currentSlideIndex + 1;
            updateNavButtons();
        }
    }

    // Add event listeners
    prevBtn.addEventListener('click', goToPrevSlide);
    nextBtn.addEventListener('click', goToNextSlide);

    // Add keyboard navigation
    document.addEventListener('keydown', function (e) {
        if (e.key === 'ArrowUp') {
            goToPrevSlide();
        } else if (e.key === 'ArrowDown') {
            goToNextSlide();
        }
    });

    // Initialize buttons
    updateNavButtons();

    // Dispatch event that slides are ready
    document.dispatchEvent(new CustomEvent('slidesReady', {
        detail: { slideCount: slides.length }
    }));
});