import "@xyflow/react/dist/style.css";
import "./style.css";
import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import { fetchInfo, watchReload } from "./api";
import { App } from "./App";
import { setServerInfo } from "./store";

createRoot(document.getElementById("root")!).render(
  <StrictMode>
    <App />
  </StrictMode>,
);

fetchInfo()
  .then(info => setServerInfo(`Runs ${info.command} in ${info.repo}`))
  .catch(() => setServerInfo("Server not reachable. Is blick running?"));
watchReload();
