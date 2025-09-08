"use strict";

const Range = ace.require("ace/range").Range;

const mode = "flux";

const fluxServerUrl = "https://flux.goto.ucsd.edu";
// const fluxServerUrl = "http://localhost:3000";

function pad(size, line_or_null) {
  if (line_or_null) {
    const line = "" + line_or_null;
    return " ".repeat(size - line.length) + line + "|";
  } else {
    return " ".repeat(size) + "|";
  }
}

function codeSnippet(codeLines, size, wall, span) {
  let result = "";
  result += wall + "\n";
  // Add the code line with the error
  const codeLine = codeLines[span.line_start - 1];
  result += pad(size, span.line_start) + ` ${codeLine}\n`;
  // Calculate and add the error pointer line
  const pointerPadding = span.column_start;
  const pointerLength = span.column_end - span.column_start;
  const pointer =
    " ".repeat(pointerPadding) +
    "^".repeat(pointerLength) +
    " " +
    (span.label || "");
  result += wall + pointer + "\n";
  result += wall + "\n";
  return result;
}

function formatErrorMessage(codeLines, errorJson) {
  const size = ("" + codeLines.length).length;

  // Extract error information
  const { message, code, level, spans, children } = errorJson;
  const errorCode = code?.code || "";

  // Start building the formatted error message
  let result = `${level.toLowerCase()}[${errorCode}]: ${message}\n`;

  // Find the primary span for the main error
  const primarySpan = spans.find((span) => span.is_primary) || spans[0];

  const wall = pad(size, null);
  if (primarySpan) {
    result += codeSnippet(codeLines, size, wall, primarySpan);
  }

  // Process child messages (like notes)
  if (children && children.length > 0) {
    for (const child of children) {
      // Add the note header
      result += `${child.level.toLowerCase()}: ${child.message}\n`;
      // Find the primary span for this child
      const childPrimarySpan =
        child.spans.find((span) => span.is_primary) || child.spans[0];
      if (childPrimarySpan && childPrimarySpan.line_start < codeLines.length) {
        result += codeSnippet(codeLines, size, wall, childPrimarySpan);
      }
    }
  }

  return result;
}

const errors = {
  // display errors as text message below panel?
  noDisplay: true,

  // indexed-table for tooltips
  table: {},

  // array of playgrounds
  playgrounds: null,

  // array of code sizes for each editor
  offsets: null,

  // initialize tooltip
  getTooltip: function () {
    var tooltip = document.getElementById("tooltip");

    if (!tooltip) {
      // Create tooltip dynamically
      tooltip = document.createElement("div");
      tooltip.className = "tooltip";
      tooltip.textContent = "Good morning";
      document.body.appendChild(tooltip);
    }
    return tooltip;
  },

  getEditor: function (index) {
    const block = this.playgrounds[index].block;
    return window.ace.edit(block);
  },

  getPlayground: function (index) {
    return this.playgrounds[index].playground;
  },

  initBlock: function (playground, block, index) {
    this.playgrounds.push({ playground: playground, block: block });
    const editor = window.ace.edit(block);
    const tooltip = this.getTooltip();

    // register mouse move
    editor.renderer.scroller.addEventListener("mousemove", function (e) {
      var pos = editor.renderer.screenToTextCoordinates(e.clientX, e.clientY);
      let text = errors.text(pos, index);
      if (text) {
        tooltip.style.position = "fixed"; // Position relative to viewport
        tooltip.style.left = e.clientX + 10 + "px";
        tooltip.style.top = e.clientY + 10 + "px";
        tooltip.textContent = text;
        tooltip.style.display = "block";
      } else {
        tooltip.style.display = "none";
      }
    });

    // register mouse leave
    editor.renderer.scroller.addEventListener("mouseleave", function () {
      tooltip.style.display = "none";
    });
  },

  // initialize editors
  initEditors: function () {
    this.playgrounds = [];
    var index = 0;
    var playgrounds = Array.from(document.querySelectorAll(".playground"));
    for (const playground of playgrounds) {
      let block = playground.querySelector("code");
      if (window.ace && block.classList.contains("editable")) {
        this.initBlock(playground, block, index);
        index += 1;
      }
    }
  },

  // initialize all flux state
  init: function () {
    if (this.playgrounds == null) {
      this.initEditors();
    }
  },

  // clear (previous) errors
  clear: function () {
    this.table = [];

    for (const index in this.playgrounds) {
      const editor = this.getEditor(index);
      // make an empty map for the error tooltips
      this.table.push({});
      // erase any previous markers
      const prevMarkers = editor.session.getMarkers();
      if (prevMarkers) {
        const prevMarkersArr = Object.keys(prevMarkers);
        for (let item of prevMarkersArr) {
          editor.session.removeMarker(prevMarkers[item].id);
        }
      }
    }
  },

  errorMessage: function (index, info) {
    // return info.message + ": " + info.explanation;
    return info.tooltipMessage;
  },

  // method to get the tooltip text
  text: function (pos, index) {
    if (this.table[index]) {
      for (const info of this.table[index][pos.row + 1] || []) {
        let matches =
          (info.pos.column_start <= pos.column &&
            pos.column <= info.pos.column_end) ||
          pos.row + 1 <= info.pos.line_end;

        if (matches) {
          return this.errorMessage(index, info);
        }
      }
    }
    return null;
  },
  playground_text: function () {
    this.init();
    var code = "";
    this.offsets = [];
    var offset = 0;
    for (const index in this.playgrounds) {
      const editor = this.getEditor(index);
      this.offsets.push(offset);
      const text = editor.getValue();
      const lines = text.split("\n").length;
      code = code + text + "\n";
      offset += lines;
    }
    this.code = code.split("\n");
    return code;
  },

  findEditorIndex(line) {
    const n = this.offsets.length;

    // Handle edge cases
    if (n === 0) return -1;
    if (line < this.offsets[0]) return -1;
    if (this.offsets[n - 1] <= line) return n - 1;

    // Binary search
    let left = 0;
    let right = n - 1;

    while (left <= right) {
      const mid = Math.floor((left + right) / 2);

      if (this.offsets[mid] <= line && line < this.offsets[mid + 1]) return mid;

      // Adjust search range
      if (this.offsets[mid] < line) {
        left = mid + 1;
      } else {
        right = mid - 1;
      }
    }

    return -1; // This should never happen with valid input
  },

  addError: function (
    errorMessages,
    index,
    line_start,
    column_start,
    line_end,
    column_end,
    info,
    err,
  ) {
    // concatenate error to errorMessages for `index`
    const currentMessage = errorMessages[index] ?? "";
    const msg = formatErrorMessage(this.code, err);
    if (currentMessage == "") {
      errorMessages[index] = msg;
    } else {
      errorMessages[index] = currentMessage + "\n" + msg;
    }

    info.tooltipMessage = msg;

    // add text for error tooltip
    const table = this.table[index];
    if (table && table[line_start] && table[line_start].length > 0) {
      table[line_start].push(info);
    } else {
      table[line_start] = [info];
    }

    // add squiggle for error
    const editor = this.getEditor(index);
    const rng = new Range(
      line_start - 1,
      column_start - 1,
      line_end - 1,
      column_end - 1,
    );
    const marker = editor.session.addMarker(rng, "ace_error", "text", false);
  },

  displayErrorMessages: function (errorMessages) {

    const playgroundsButton = document.querySelector('button[title="Playgrounds"][aria-label="Playgrounds"]');
    playgroundsButton.style.color = "";

    for (const index in this.playgrounds) {
      const code_block = this.getPlayground(index);

      const result = errorMessages[index] ?? "";

      var result_block = code_block.querySelector(".result");
      if (!result_block) {
        result_block = document.createElement("code");
        result_block.className = "result hljs language-bash";
        code_block.append(result_block);
      }

      if (result.trim() === "") {
        code_block.classList.remove("unsafe");
      } else {
        code_block.classList.add("unsafe");
        playgroundsButton.style.color = "red";
      }

      if (result.trim() === "" || this.noDisplay) {
        result_block.style.display = "none";
        result_block.innerText = "Safe";
        result_block.classList.add("result-no-output");
      } else {
        result_block.style.display = "block";
        result_block.innerText = result;
        result_block.classList.remove("result-no-output");
      }
    }
  },

  // update editors with (new) errors from a response
  update: function (response) {
    this.init();
    this.clear();
    let errorMessages = {};
    for (const err of response.errors) {
      if (err.level == "Error" && err.spans.length > 0) {
        const span = err.spans[0];
        const index = this.findEditorIndex(span.line_start);
        if (index != -1) {
          const offset = this.offsets[index];
          const line_start = span.line_start - offset;
          const line_end = span.line_end - offset;

          // update table for tooltips
          const single = line_start == line_end;
          const position = single
            ? { column_start: span.column_start, column_end: span.column_end }
            : { line_end: span.line_end };
          const info = {
            pos: position,
            message: err.message,
            explanation: span.label,
          };
          this.addError(
            errorMessages,
            index,
            line_start,
            span.column_start,
            line_end,
            span.column_end,
            info,
            err,
          );
        }
      }
    }
    this.displayErrorMessages(errorMessages);
  },
};

const queryFlux = {
  url() {
    return fluxServerUrl + "/api/verify";
  },

  result(code_block, result_block, response) {
    console.log('TRACE: queryFlux', code_block, result_block, response);
    errors.update(response);
  },

  playground_text(playground, hidden = true) {
    return errors.playground_text();
  },
};

const queryRust = {
  url() {
    return "https://play.rust-lang.org/evaluate.json";
  },

  result(code_block, result_block, response) {
    const result = response.result;
    if (result.trim() === "") {
      result_block.innerText = "No output";
      result_block.classList.add("result-no-output");
    } else {
      result_block.innerText = result;
      result_block.classList.remove("result-no-output");
    }
  },

  playground_text(playground, hidden = true) {
    return playground_text(playground, hidden);
  },
};

const query = queryFlux;

// Fix back button cache problem
window.onunload = function () { };

// Global variable, shared between modules
function playground_text(playground, hidden = true) {
  let code_block = playground.querySelector("code");
  if (window.ace && code_block.classList.contains("editable")) {
    let editor = window.ace.edit(code_block);
    return editor.getValue();
  } else if (hidden) {
    return code_block.textContent;
  } else {
    return code_block.innerText;
  }
}

(function codeSnippets() {
  function fetch_with_timeout(url, options, timeout = 6000) {
    return Promise.race([
      fetch(url, options),
      new Promise((_, reject) =>
        setTimeout(() => reject(new Error("timeout")), timeout),
      ),
    ]);
  }

  var playgrounds = Array.from(document.querySelectorAll(".playground"));
  if (playgrounds.length > 0) {
    fetch_with_timeout("https://play.rust-lang.org/meta/crates", {
      headers: {
        "Content-Type": "application/json",
      },
      method: "POST",
      mode: "cors",
    })
      .then((response) => response.json())
      .then((response) => {
        // get list of crates available in the rust playground
        let playground_crates = response.crates.map((item) => item["id"]);
        playgrounds.forEach((block) =>
          handle_crate_list_update(block, playground_crates),
        );
      });
  }

  function handle_crate_list_update(playground_block, playground_crates) {
    // update the play buttons after receiving the response
    update_play_button(playground_block, playground_crates);

    // and install on change listener to dynamically update ACE editors
    if (window.ace) {
      let code_block = playground_block.querySelector("code");
      if (code_block.classList.contains("editable")) {
        let editor = window.ace.edit(code_block);
        editor.addEventListener("change", function (e) {
          update_play_button(playground_block, playground_crates);
        });
        // add Ctrl-Enter command to execute rust code
        editor.commands.addCommand({
          name: "run",
          bindKey: {
            win: "Ctrl-Enter",
            mac: "Ctrl-Enter",
          },
          exec: (_editor) => run_rust_code(playground_block),
        });
      }
    }
  }

  // updates the visibility of play button based on `no_run` class and
  // used crates vs ones available on https://play.rust-lang.org
  function update_play_button(pre_block, playground_crates) {
    var play_button = pre_block.querySelector(".play-button");

    // skip if code is `no_run`
    if (pre_block.querySelector("code").classList.contains("no_run")) {
      play_button.classList.add("hidden");
      return;
    }

    // get list of `extern crate`'s from snippet
    var txt = playground_text(pre_block);
    var re = /extern\s+crate\s+([a-zA-Z_0-9]+)\s*;/g;
    var snippet_crates = [];
    var item;
    while ((item = re.exec(txt))) {
      snippet_crates.push(item[1]);
    }

    // check if all used crates are available on play.rust-lang.org
    var all_available = snippet_crates.every(function (elem) {
      return playground_crates.indexOf(elem) > -1;
    });

    if (all_available) {
      play_button.classList.remove("hidden");
    } else {
      play_button.classList.add("hidden");
    }
  }

  function run_rust_code(code_block) {
    console.log("TRACE: run_rust_code", code_block);
    var result_block = code_block.querySelector(".result");
    if (!result_block) {
      result_block = document.createElement("code");
      result_block.className = "result hljs language-bash";

      code_block.append(result_block);
    }

    let text = query.playground_text(code_block);
    let classes = code_block.querySelector("code").classList;
    let edition = "2015";
    if (classes.contains("edition2018")) {
      edition = "2018";
    } else if (classes.contains("edition2021")) {
      edition = "2021";
    }
    var params = {
      version: "stable",
      optimize: "0",
      code: text,
      edition: edition,
      crateType: "rlib",
    };
    console.log('TRACE: query code', text);

    if (text.indexOf("#![feature") !== -1) {
      params.version = "nightly";
    }

    result_block.innerText = "Running...";

    fetch_with_timeout(query.url(), {
      headers: {
        "Content-Type": "application/json",
      },
      method: "POST",
      mode: "cors",
      body: JSON.stringify(params),
    })
      .then((response) => response.json())
      .then((response) => {
        query.result(code_block, result_block, response);
      })
      .catch(
        (error) =>
        (result_block.innerText =
          "Playground Communication: " + error.message),
      );
  }

  // Syntax highlighting Configuration
  hljs.configure({
    tabReplace: "    ", // 4 spaces
    languages: [], // Languages used for auto-detection
  });

  let code_nodes = Array.from(document.querySelectorAll("code"))
    // Don't highlight `inline code` blocks in headers.
    .filter(function (node) {
      return !node.parentElement.classList.contains("header");
    });

  if (window.ace) {
    // language-rust class needs to be removed for editable
    // blocks or highlightjs will capture events
    code_nodes
      .filter(function (node) {
        return node.classList.contains("editable");
      })
      .forEach(function (block) {
        block.classList.remove("language-rust");
      });

    code_nodes
      .filter(function (node) {
        return !node.classList.contains("editable");
      })
      .forEach(function (block) {
        hljs.highlightBlock(block);
      });
  } else {
    code_nodes.forEach(function (block) {
      hljs.highlightBlock(block);
    });
  }

  // Adding the hljs class gives code blocks the color css
  // even if highlighting doesn't apply
  code_nodes.forEach(function (block) {
    block.classList.add("hljs");
  });

  Array.from(document.querySelectorAll("code.hljs")).forEach(function (block) {
    var lines = Array.from(block.querySelectorAll(".boring"));
    // If no lines were hidden, return
    if (!lines.length) {
      return;
    }
    block.classList.add("hide-boring");

    var buttons = document.createElement("div");
    buttons.className = "buttons";
    buttons.innerHTML =
      '<button class="fa fa-eye" title="Show hidden lines" aria-label="Show hidden lines"></button>';

    // add expand button
    var pre_block = block.parentNode;
    pre_block.insertBefore(buttons, pre_block.firstChild);

    pre_block.querySelector(".buttons").addEventListener("click", function (e) {
      if (e.target.classList.contains("fa-eye")) {
        e.target.classList.remove("fa-eye");
        e.target.classList.add("fa-eye-slash");
        e.target.title = "Hide lines";
        e.target.setAttribute("aria-label", e.target.title);

        block.classList.remove("hide-boring");
      } else if (e.target.classList.contains("fa-eye-slash")) {
        e.target.classList.remove("fa-eye-slash");
        e.target.classList.add("fa-eye");
        e.target.title = "Show hidden lines";
        e.target.setAttribute("aria-label", e.target.title);

        block.classList.add("hide-boring");
      }
    });
  });

  if (window.playground_copyable) {
    Array.from(document.querySelectorAll("pre code")).forEach(function (block) {
      var pre_block = block.parentNode;
      if (!pre_block.classList.contains("playground")) {
        var buttons = pre_block.querySelector(".buttons");
        if (!buttons) {
          buttons = document.createElement("div");
          buttons.className = "buttons";
          pre_block.insertBefore(buttons, pre_block.firstChild);
        }

        var clipButton = document.createElement("button");
        clipButton.className = "fa fa-copy clip-button";
        clipButton.title = "Copy to clipboard";
        clipButton.setAttribute("aria-label", clipButton.title);
        clipButton.innerHTML = '<i class=\"tooltiptext\"></i>';

        buttons.insertBefore(clipButton, buttons.firstChild);
      }
    });
  }

  // Process playground code blocks
  Array.from(document.querySelectorAll(".playground")).forEach(
    function (pre_block) {
      // Add play button
      var buttons = pre_block.querySelector(".buttons");
      if (!buttons) {
        buttons = document.createElement("div");
        buttons.className = "buttons";
        pre_block.insertBefore(buttons, pre_block.firstChild);
      }

      var runCodeButton = document.createElement("button");
      runCodeButton.className = "fa fa-play play-button";
      runCodeButton.hidden = true;
      runCodeButton.title = "Run this code";
      runCodeButton.setAttribute("aria-label", runCodeButton.title);

      buttons.insertBefore(runCodeButton, buttons.firstChild);
      runCodeButton.addEventListener("click", function (e) {
        run_rust_code(pre_block);
      });

      if (window.playground_copyable) {
        var copyCodeClipboardButton = document.createElement("button");
        copyCodeClipboardButton.className = "fa fa-copy clip-button";
        copyCodeClipboardButton.innerHTML = '<i class="tooltiptext"></i>';
        copyCodeClipboardButton.title = "Copy to clipboard";
        copyCodeClipboardButton.setAttribute(
          "aria-label",
          copyCodeClipboardButton.title,
        );

        buttons.insertBefore(copyCodeClipboardButton, buttons.firstChild);
      }

      let code_block = pre_block.querySelector("code");
      if (window.ace && code_block.classList.contains("editable")) {
        var undoChangesButton = document.createElement("button");
        undoChangesButton.className = "fa fa-history reset-button";
        undoChangesButton.title = "Undo changes";
        undoChangesButton.setAttribute("aria-label", undoChangesButton.title);

        buttons.insertBefore(undoChangesButton, buttons.firstChild);

        undoChangesButton.addEventListener("click", function () {
          let editor = window.ace.edit(code_block);
          editor.setValue(editor.originalCode);
          editor.clearSelection();
        });
      }
    },
  );
})();

(function themes() {
  var html = document.querySelector("html");
  var themeToggleButton = document.getElementById("theme-toggle");
  var themePopup = document.getElementById("theme-list");
  var themeColorMetaTag = document.querySelector('meta[name="theme-color"]');
  var stylesheets = {
    ayuHighlight: document.querySelector("[href$='ayu-highlight.css']"),
    tomorrowNight: document.querySelector("[href$='tomorrow-night.css']"),
    highlight: document.querySelector("[href$='highlight.css']"),
  };

  function showThemes() {
    themePopup.style.display = "block";
    themeToggleButton.setAttribute("aria-expanded", true);
    themePopup.querySelector("button#" + get_theme()).focus();
  }

  function updateThemeSelected() {
    themePopup.querySelectorAll(".theme-selected").forEach(function (el) {
      el.classList.remove("theme-selected");
    });
    themePopup
      .querySelector("button#" + get_theme())
      .classList.add("theme-selected");
  }

  function hideThemes() {
    themePopup.style.display = "none";
    themeToggleButton.setAttribute("aria-expanded", false);
    themeToggleButton.focus();
  }

  function get_theme() {
    var theme;
    try {
      theme = localStorage.getItem("mdbook-theme");
    } catch (e) { }
    if (theme === null || theme === undefined) {
      return default_theme;
    } else {
      return theme;
    }
  }

  function set_theme(theme, store = true) {
    let ace_theme;

    if (theme == "coal" || theme == "navy") {
      stylesheets.ayuHighlight.disabled = true;
      stylesheets.tomorrowNight.disabled = false;
      stylesheets.highlight.disabled = true;

      ace_theme = "ace/theme/tomorrow_night";
    } else if (theme == "ayu") {
      stylesheets.ayuHighlight.disabled = false;
      stylesheets.tomorrowNight.disabled = true;
      stylesheets.highlight.disabled = true;
      ace_theme = "ace/theme/tomorrow_night";
    } else {
      stylesheets.ayuHighlight.disabled = true;
      stylesheets.tomorrowNight.disabled = true;
      stylesheets.highlight.disabled = false;
      ace_theme = "ace/theme/dawn";
    }

    setTimeout(function () {
      themeColorMetaTag.content = getComputedStyle(
        document.documentElement,
      ).backgroundColor;
    }, 1);

    if (window.ace && window.editors) {
      window.editors.forEach(function (editor) {
        editor.setTheme(ace_theme);
      });
    }

    var previousTheme = get_theme();

    if (store) {
      try {
        localStorage.setItem("mdbook-theme", theme);
      } catch (e) { }
    }

    html.classList.remove(previousTheme);
    html.classList.add(theme);
    updateThemeSelected();
  }

  // Set theme
  var theme = get_theme();

  set_theme(theme, false);

  themeToggleButton.addEventListener("click", function () {
    if (themePopup.style.display === "block") {
      hideThemes();
    } else {
      showThemes();
    }
  });

  themePopup.addEventListener("click", function (e) {
    var theme;
    if (e.target.className === "theme") {
      theme = e.target.id;
    } else if (e.target.parentElement.className === "theme") {
      theme = e.target.parentElement.id;
    } else {
      return;
    }
    set_theme(theme);
  });

  themePopup.addEventListener("focusout", function (e) {
    // e.relatedTarget is null in Safari and Firefox on macOS (see workaround below)
    if (
      !!e.relatedTarget &&
      !themeToggleButton.contains(e.relatedTarget) &&
      !themePopup.contains(e.relatedTarget)
    ) {
      hideThemes();
    }
  });

  // Should not be needed, but it works around an issue on macOS & iOS: https://github.com/rust-lang/mdBook/issues/628
  document.addEventListener("click", function (e) {
    if (
      themePopup.style.display === "block" &&
      !themeToggleButton.contains(e.target) &&
      !themePopup.contains(e.target)
    ) {
      hideThemes();
    }
  });

  document.addEventListener("keydown", function (e) {
    if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) {
      return;
    }
    if (!themePopup.contains(e.target)) {
      return;
    }

    switch (e.key) {
      case "Escape":
        e.preventDefault();
        hideThemes();
        break;
      case "ArrowUp":
        e.preventDefault();
        var li = document.activeElement.parentElement;
        if (li && li.previousElementSibling) {
          li.previousElementSibling.querySelector("button").focus();
        }
        break;
      case "ArrowDown":
        e.preventDefault();
        var li = document.activeElement.parentElement;
        if (li && li.nextElementSibling) {
          li.nextElementSibling.querySelector("button").focus();
        }
        break;
      case "Home":
        e.preventDefault();
        themePopup.querySelector("li:first-child button").focus();
        break;
      case "End":
        e.preventDefault();
        themePopup.querySelector("li:last-child button").focus();
        break;
    }
  });
})();

(function sidebar() {
  var body = document.querySelector("body");
  var sidebar = document.getElementById("sidebar");
  var sidebarLinks = document.querySelectorAll("#sidebar a");
  var sidebarToggleButton = document.getElementById("sidebar-toggle");
  var sidebarResizeHandle = document.getElementById("sidebar-resize-handle");
  var firstContact = null;

  function showSidebar() {
    body.classList.remove("sidebar-hidden");
    body.classList.add("sidebar-visible");
    Array.from(sidebarLinks).forEach(function (link) {
      link.setAttribute("tabIndex", 0);
    });
    sidebarToggleButton.setAttribute("aria-expanded", true);
    sidebar.setAttribute("aria-hidden", false);
    try {
      localStorage.setItem("mdbook-sidebar", "visible");
    } catch (e) { }
  }

  var sidebarAnchorToggles = document.querySelectorAll("#sidebar a.toggle");

  function toggleSection(ev) {
    ev.currentTarget.parentElement.classList.toggle("expanded");
  }

  Array.from(sidebarAnchorToggles).forEach(function (el) {
    el.addEventListener("click", toggleSection);
  });

  function hideSidebar() {
    body.classList.remove("sidebar-visible");
    body.classList.add("sidebar-hidden");
    Array.from(sidebarLinks).forEach(function (link) {
      link.setAttribute("tabIndex", -1);
    });
    sidebarToggleButton.setAttribute("aria-expanded", false);
    sidebar.setAttribute("aria-hidden", true);
    try {
      localStorage.setItem("mdbook-sidebar", "hidden");
    } catch (e) { }
  }

  // Toggle sidebar
  sidebarToggleButton.addEventListener("click", function sidebarToggle() {
    if (body.classList.contains("sidebar-hidden")) {
      var current_width = parseInt(
        document.documentElement.style.getPropertyValue("--sidebar-width"),
        10,
      );
      if (current_width < 150) {
        document.documentElement.style.setProperty("--sidebar-width", "150px");
      }
      showSidebar();
    } else if (body.classList.contains("sidebar-visible")) {
      hideSidebar();
    } else {
      if (getComputedStyle(sidebar)["transform"] === "none") {
        hideSidebar();
      } else {
        showSidebar();
      }
    }
  });

  sidebarResizeHandle.addEventListener("mousedown", initResize, false);

  function initResize(e) {
    window.addEventListener("mousemove", resize, false);
    window.addEventListener("mouseup", stopResize, false);
    body.classList.add("sidebar-resizing");
  }
  function resize(e) {
    var pos = e.clientX - sidebar.offsetLeft;
    if (pos < 20) {
      hideSidebar();
    } else {
      if (body.classList.contains("sidebar-hidden")) {
        showSidebar();
      }
      pos = Math.min(pos, window.innerWidth - 100);
      document.documentElement.style.setProperty("--sidebar-width", pos + "px");
    }
  }
  //on mouseup remove windows functions mousemove & mouseup
  function stopResize(e) {
    body.classList.remove("sidebar-resizing");
    window.removeEventListener("mousemove", resize, false);
    window.removeEventListener("mouseup", stopResize, false);
  }

  document.addEventListener(
    "touchstart",
    function (e) {
      firstContact = {
        x: e.touches[0].clientX,
        time: Date.now(),
      };
    },
    { passive: true },
  );

  document.addEventListener(
    "touchmove",
    function (e) {
      if (!firstContact) return;

      var curX = e.touches[0].clientX;
      var xDiff = curX - firstContact.x,
        tDiff = Date.now() - firstContact.time;

      if (tDiff < 250 && Math.abs(xDiff) >= 150) {
        if (
          xDiff >= 0 &&
          firstContact.x < Math.min(document.body.clientWidth * 0.25, 300)
        )
          showSidebar();
        else if (xDiff < 0 && curX < 300) hideSidebar();

        firstContact = null;
      }
    },
    { passive: true },
  );
})();

(function chapterNavigation() {
  document.addEventListener("keydown", function (e) {
    if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) {
      return;
    }
    if (window.search && window.search.hasFocus()) {
      return;
    }
    var html = document.querySelector("html");

    function next() {
      var nextButton = document.querySelector(".nav-chapters.next");
      if (nextButton) {
        window.location.href = nextButton.href;
      }
    }
    function prev() {
      var previousButton = document.querySelector(".nav-chapters.previous");
      if (previousButton) {
        window.location.href = previousButton.href;
      }
    }
    switch (e.key) {
      case "ArrowRight":
        e.preventDefault();
        if (html.dir == "rtl") {
          prev();
        } else {
          next();
        }
        break;
      case "ArrowLeft":
        e.preventDefault();
        if (html.dir == "rtl") {
          next();
        } else {
          prev();
        }
        break;
    }
  });
})();

(function clipboard() {
  var clipButtons = document.querySelectorAll(".clip-button");

  function hideTooltip(elem) {
    elem.firstChild.innerText = "";
    elem.className = "fa fa-copy clip-button";
  }

  function showTooltip(elem, msg) {
    elem.firstChild.innerText = msg;
    elem.className = "fa fa-copy tooltipped";
  }

  var clipboardSnippets = new ClipboardJS(".clip-button", {
    text: function (trigger) {
      hideTooltip(trigger);
      let playground = trigger.closest("pre");
      return playground_text(playground, false);
    },
  });

  Array.from(clipButtons).forEach(function (clipButton) {
    clipButton.addEventListener("mouseout", function (e) {
      hideTooltip(e.currentTarget);
    });
  });

  clipboardSnippets.on("success", function (e) {
    e.clearSelection();
    showTooltip(e.trigger, "Copied!");
  });

  clipboardSnippets.on("error", function (e) {
    showTooltip(e.trigger, "Clipboard error!");
  });
})();

(function scrollToTop() {
  var menuTitle = document.querySelector(".menu-title");

  menuTitle.addEventListener("click", function () {
    document.scrollingElement.scrollTo({ top: 0, behavior: "smooth" });
  });
})();

(function controllMenu() {
  var menu = document.getElementById("menu-bar");

  (function controllPosition() {
    var scrollTop = document.scrollingElement.scrollTop;
    var prevScrollTop = scrollTop;
    var minMenuY = -menu.clientHeight - 50;
    // When the script loads, the page can be at any scroll (e.g. if you reforesh it).
    menu.style.top = scrollTop + "px";
    // Same as parseInt(menu.style.top.slice(0, -2), but faster
    var topCache = menu.style.top.slice(0, -2);
    menu.classList.remove("sticky");
    var stickyCache = false; // Same as menu.classList.contains('sticky'), but faster
    document.addEventListener(
      "scroll",
      function () {
        scrollTop = Math.max(document.scrollingElement.scrollTop, 0);
        // `null` means that it doesn't need to be updated
        var nextSticky = null;
        var nextTop = null;
        var scrollDown = scrollTop > prevScrollTop;
        var menuPosAbsoluteY = topCache - scrollTop;
        if (scrollDown) {
          nextSticky = false;
          if (menuPosAbsoluteY > 0) {
            nextTop = prevScrollTop;
          }
        } else {
          if (menuPosAbsoluteY > 0) {
            nextSticky = true;
          } else if (menuPosAbsoluteY < minMenuY) {
            nextTop = prevScrollTop + minMenuY;
          }
        }
        if (nextSticky === true && stickyCache === false) {
          menu.classList.add("sticky");
          stickyCache = true;
        } else if (nextSticky === false && stickyCache === true) {
          menu.classList.remove("sticky");
          stickyCache = false;
        }
        if (nextTop !== null) {
          menu.style.top = nextTop + "px";
          topCache = nextTop;
        }
        prevScrollTop = scrollTop;
      },
      { passive: true },
    );
  })();
  (function controllBorder() {
    function updateBorder() {
      if (menu.offsetTop === 0) {
        menu.classList.remove("bordered");
      } else {
        menu.classList.add("bordered");
      }
    }
    updateBorder();
    document.addEventListener("scroll", updateBorder, { passive: true });
  })();
})();

(function addPlaygroundsButton() {
  var leftButtons = document.querySelector(".left-buttons");
  if (leftButtons) {
    var playgroundsButton = document.createElement("button");
    playgroundsButton.className = "icon-button";
    playgroundsButton.type = "button";
    playgroundsButton.title = "Playgrounds";
    playgroundsButton.setAttribute("aria-label", "Playgrounds");
    playgroundsButton.setAttribute("aria-haspopup", "true");
    playgroundsButton.setAttribute("aria-expanded", "false");
    playgroundsButton.setAttribute("aria-keyshortcuts", "Control+e");

    var icon = document.createElement("i");
    icon.className = "fa fa-code";
    icon.setAttribute("aria-hidden", "true");

    playgroundsButton.appendChild(icon);
    leftButtons.appendChild(playgroundsButton);

    // Create dropdown
    var dropdown = document.createElement("div");
    dropdown.className = "playgrounds-dropdown";
    dropdown.style.display = "none";
    dropdown.style.position = "fixed";
    dropdown.style.backgroundColor = "var(--bg)";
    dropdown.style.border = "1px solid var(--sidebar-bg)";
    dropdown.style.borderRadius = "4px";
    dropdown.style.boxShadow = "0 2px 8px rgba(0,0,0,0.15)";
    dropdown.style.padding = "8px 0";
    dropdown.style.minWidth = "60px";
    dropdown.style.zIndex = "1000";

    leftButtons.appendChild(dropdown);

    function updateDropdownItems() {
      // Clear existing items
      dropdown.innerHTML = "";

      // Find all unsafe playgrounds
      var playgrounds = Array.from(document.querySelectorAll(".playground"));
      var unsafeIndexes = [];

      playgrounds.forEach(function (playground, index) {
        if (playground.classList.contains("unsafe")) {
          unsafeIndexes.push(index);
        }
      });

      if (unsafeIndexes.length === 0) {
        var noItems = document.createElement("div");
        noItems.textContent = "No unsafe playgrounds";
        noItems.style.padding = "8px 16px";
        noItems.style.color = "var(--fg)";
        noItems.style.fontStyle = "italic";
        dropdown.appendChild(noItems);
      } else {
        unsafeIndexes.forEach(function (index) {
          var item = document.createElement("button");
          item.className = "dropdown-item";
          item.textContent = index;
          item.style.display = "block";
          item.style.width = "100%";
          item.style.padding = "8px 16px";
          item.style.border = "none";
          item.style.backgroundColor = "transparent";
          item.style.color = "var(--fg)";
          item.style.cursor = "pointer";
          item.style.textAlign = "left";

          item.addEventListener("mouseover", function () {
            item.style.backgroundColor = "var(--sidebar-bg)";
          });

          item.addEventListener("mouseout", function () {
            item.style.backgroundColor = "transparent";
          });

          item.addEventListener("click", function () {
            console.log("Selected unsafe playground:", index);

            // Scroll to the selected playground
            var playgrounds = Array.from(document.querySelectorAll(".playground"));
            if (playgrounds[index]) {
              playgrounds[index].scrollIntoView({
                behavior: "smooth",
                block: "center",
                inline: "nearest"
              });
            }

            dropdown.style.display = "none";
          });

          dropdown.appendChild(item);
        });
      }
    }

    // Toggle dropdown on button click
    playgroundsButton.addEventListener("click", function (e) {
      e.stopPropagation();
      if (dropdown.style.display === "none") {
        // Update items before showing
        updateDropdownItems();

        // Position dropdown below button
        var rect = playgroundsButton.getBoundingClientRect();
        dropdown.style.top = rect.bottom + "px";
        dropdown.style.left = rect.left + "px";
        dropdown.style.display = "block";
      } else {
        dropdown.style.display = "none";
      }
    });

    // Close dropdown when clicking outside
    document.addEventListener("click", function () {
      dropdown.style.display = "none";
    });

    // Add keyboard shortcut (Ctrl+E) to toggle dropdown
    document.addEventListener("keydown", function (e) {
      if (e.ctrlKey && e.key.toLowerCase() === 'e') {
        e.preventDefault();
        playgroundsButton.click();
      }
    });
  }
})();
