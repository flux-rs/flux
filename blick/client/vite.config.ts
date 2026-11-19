import react from "@vitejs/plugin-react";
import { defineConfig } from "vite";

// `blick` runs `vite build --watch` and serves `dist/` itself (see `src/main.rs` in the
// crate), so there is no dev server here.
export default defineConfig({
  plugins: [react()],
  build: {
    outDir: "dist",
    emptyOutDir: true,
    sourcemap: true,
    // elkjs alone is about 1.5 MB; the page is served locally
    chunkSizeWarningLimit: 4000,
    rolldownOptions: {
      onwarn(warning, warn) {
        // React Flow's "use no memo" directive, which only matters to the React compiler
        if (warning.code === "MODULE_LEVEL_DIRECTIVE") return;
        warn(warning);
      },
    },
  },
});
