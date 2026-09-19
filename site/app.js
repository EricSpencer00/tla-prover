const endpoint = "https://tla-runner.ericspencer.us";
const source = document.querySelector("#tla-source");
const output = document.querySelector("#run-output");
const runButton = document.querySelector("#run-parse");
const resetButton = document.querySelector("#reset-source");
const health = document.querySelector(".runner-health");
const healthLabel = document.querySelector("#health-label");
const runTime = document.querySelector("#run-time");
const runLedger = document.querySelector("#run-ledger");
const methodMatrix = document.querySelector("#method-matrix");
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

function statusClass(status) {
  return {
    available: "ready",
    published: "ready",
    measured: "ready",
    baseline: "active",
    open: "active",
    shelved: "active",
    failed: "failed",
    retracted: "failed",
    not_run: "active",
  }[status] || "active";
}

function renderRunLedger(runs) {
  if (!runLedger) return;
  if (!Array.isArray(runs) || !runs.length) {
    runLedger.innerHTML = "<p>No published run snapshot is available.</p>";
    return;
  }
  runLedger.innerHTML = runs.map((run) => {
    const evidence = run.evidence
      ? ` <a href="https://github.com/LUC-AI4FM/tla-prover/blob/main/${encodeURI(run.evidence)}">Read evidence ↗</a>`
      : "";
    return `<article><time>${escapeHTML(run.id || "run")}</time><div><span class="state ${statusClass(run.status)}">${escapeHTML((run.status || "unknown").replaceAll("_", " "))}</span><h3>${escapeHTML(run.label || run.id || "Unnamed run")}</h3><p><b>${escapeHTML(run.result || "No result recorded.")}</b> ${escapeHTML(run.meaning || "")}${evidence}</p></div></article>`;
  }).join("");
}

function renderMethodMatrix(rows) {
  if (!methodMatrix) return;
  if (!Array.isArray(rows) || !rows.length) {
    methodMatrix.innerHTML = "<tr><td colspan=\"5\">No method snapshot is available.</td></tr>";
    return;
  }
  methodMatrix.innerHTML = rows.map((row) => `<tr>
    <td><strong>${escapeHTML(row.base_model)}</strong></td>
    <td><strong>${escapeHTML(row.method)}</strong><small>${escapeHTML(row.run)}</small></td>
    <td>${escapeHTML(row.update_scope)}</td>
    <td>${escapeHTML(row.outcome)}</td>
    <td><span class="state ${statusClass(row.status)}">${escapeHTML(row.status.replaceAll("_", " "))}</span><small>${escapeHTML(row.claim)}</small></td>
  </tr>`).join("");
}

async function loadPublishedStatus() {
  try {
    const response = await fetch("status.json", { headers: { accept: "application/json" }, cache: "no-store" });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const data = await response.json();
    const program = data.program || {};
    const phase = document.querySelector("#program-phase");
    const gate = document.querySelector("#program-gate");
    const snapshot = document.querySelector("#snapshot-date");
    const note = document.querySelector("#snapshot-note");
    if (phase) phase.textContent = program.phase || "Unknown";
    if (gate) gate.textContent = `${program.gate || "—"} ${program.gate_label || ""}`.trim();
    if (snapshot) snapshot.textContent = data.published_at || "Unknown";
    if (note) note.textContent = data.freshness_note || "Published snapshot; use the notebook for a fresh probe.";
    renderRunLedger(data.training_runs);
    renderMethodMatrix(data.model_matrix);
  } catch (error) {
    const note = document.querySelector("#snapshot-note");
    if (note) note.textContent = "Published snapshot unavailable; repository evidence remains the source of truth.";
    renderRunLedger([]);
    renderMethodMatrix([]);
  }
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
loadPublishedStatus();
