const endpoint = "https://tla-runner.ericspencer.us";
const source = document.querySelector("#tla-source");
const output = document.querySelector("#run-output");
const runButton = document.querySelector("#run-parse");
const resetButton = document.querySelector("#reset-source");
const health = document.querySelector(".runner-health");
const healthLabel = document.querySelector("#health-label");
const runTime = document.querySelector("#run-time");
const initialSource = source.value;

function escapeHTML(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

async function checkHealth() {
  try {
    const response = await fetch(`${endpoint}/health`, { headers: { accept: "application/json" } });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const data = await response.json();
    health.classList.add("online");
    healthLabel.textContent = data.ok ? "TLAKit runner online" : "Runner responding";
  } catch (error) {
    health.classList.add("offline");
    healthLabel.textContent = "Runner unavailable";
  }
}

function renderResult(data, elapsed) {
  const diagnostics = Array.isArray(data.diagnostics) ? data.diagnostics : [];
  const ok = data.outcome === "ok" && diagnostics.every((item) => item.severity !== "error");
  const rows = diagnostics.length
    ? diagnostics.map((item) => `<div class="diagnostic"><b>${escapeHTML(item.severity || "diagnostic")}</b><p>${escapeHTML(item.message || "No message")}</p>${item.line ? `<small>Line ${escapeHTML(item.line)}${item.column ? `, column ${escapeHTML(item.column)}` : ""}</small>` : ""}</div>`).join("")
    : "<p>No diagnostics returned.</p>";
  output.className = "";
  output.innerHTML = `<div class="result-banner ${ok ? "ok" : "error"}">${ok ? "SANY PASS" : "CHECK FAILED"}</div>${rows}`;
  runTime.textContent = `${elapsed} ms`;
}

async function runParse() {
  runButton.disabled = true;
  runButton.textContent = "Checking…";
  output.className = "empty-output";
  output.innerHTML = "<strong>Running.</strong><p>Waiting for the isolated TLAKit runner.</p>";
  const started = performance.now();
  try {
    const response = await fetch(`${endpoint}/parse`, {
      method: "POST",
      headers: { "content-type": "application/json", accept: "application/json" },
      body: JSON.stringify({ spec: source.value }),
    });
    const data = await response.json();
    if (!response.ok) throw new Error(data.detail || `Runner returned HTTP ${response.status}`);
    renderResult(data, Math.round(performance.now() - started));
  } catch (error) {
    output.className = "";
    output.innerHTML = `<div class="result-banner error">RUNNER ERROR</div><p>${escapeHTML(error.message)}</p>`;
    runTime.textContent = `${Math.round(performance.now() - started)} ms`;
  } finally {
    runButton.disabled = false;
    runButton.textContent = "Run SANY check";
  }
}

runButton.addEventListener("click", runParse);
resetButton.addEventListener("click", () => {
  source.value = initialSource;
  source.focus();
});
checkHealth();
