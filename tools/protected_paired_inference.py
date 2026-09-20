"""Frozen two-arm inference driver for protected rows 47 and 107.

The driver is deliberately endpoint-oriented: it never changes model weights,
and it records the exact request/response evidence needed before SANY scoring.
The grammar arm must be enabled by the serving endpoint; the receipt records
the transport field used so a preflight can verify it independently.
"""
import argparse, hashlib, json, os, sys, time
from pathlib import Path
from urllib.request import Request, urlopen

ROWS = (47, 107)
ARMS = ("existing_decoder", "grammar_enforced")
EOS_IDS = (128001, 128008, 128009)
# Small, separately identified prompt intervention for the post-baseline retry.
# It does not alter the recovered prompt or its hash; the receipt records the
# derived prompt hash and intervention so the frozen baseline remains intact.
SYNTAX_REPAIR_SUFFIX = (
    "\n\nReturn only the complete TLA+ module. Before finishing, check that "
    "every declaration is separated, every sequence/function annotation is "
    "syntactically valid TLA+, and the module parses with SANY. Do not use a "
    "type annotation after an empty sequence; use an expression valid in TLA+."
)
STRUCTURAL_REPAIR_SUFFIX = (
    "\n\nReturn only the complete TLA+ module and perform a final SANY syntax "
    "check. Use TLA+ operators exactly: function/set mappings use "
    "[x \\in S |-> expr] (never [x IN S |-> expr]); terminate each top-level "
    "definition before the next declaration, and put a blank line before "
    "SPECIFICATION, VARIABLES, or any other top-level keyword. Do not emit "
    "a prose explanation, type annotation, or markdown fence."
)
DECLARATION_SCHEMA_SUFFIX = (
    "\n\nReturn exactly one complete TLA+ module using this top-level schema: "
    "module header, CONSTANTS (if needed), VARIABLES (one identifier per line), "
    "a blank line, definitions, a blank line, SPECIFICATION, then PROPERTIES. "
    "Every definition must end before the next top-level section. Use literal "
    "TLA+ syntax only: \\in (never IN), <<x>> for a sequence value (never "
    "<<>>: Type), and put each conjunction on its own line with /\\. Do not "
    "place any declaration keyword or SPECIFICATION inside an expression, and "
    "do not emit prose or markdown fences."
)
SEPARATOR_AWARE_SUFFIX = (
    "\n\nOutput the complete TLA+ module as plain text with REAL newline characters. "
    "Never output the two-character escape \\n or the four-character text \\n\\n. "
    "Use this exact section order, each separated by a blank real line: MODULE header; "
    "CONSTANTS; VARIABLES; definitions; SPECIFICATION; PROPERTIES. "
    "A definition ends at its real newline before the next definition or section. "
    "Put one conjunction per real line using /\\, and use only valid TLA+ forms such as "
    "[d \\in Dispatchers |-> 0]. Return no markdown, prose, or escaped formatting."
)
COMPACT_MODULE_SUFFIX = (
    "\n\nReturn a short, complete TLA+ module that fits comfortably in the token limit. "
    "Use each top-level definition exactly once; define one concise Init and one concise "
    "Next, and do not repeat examples or alternative definitions. Preserve the requested "
    "variables and constants, but omit optional commentary and redundant properties. "
    "Every definition must be complete before the next keyword. Emit exactly one Next "
    "definition and never repeat the word Next after it. Use plain TLA+ only, with real "
    "newlines, and stop immediately after the final property. No markdown or prose."
)
SECTION_CONTRACT_SUFFIX = (
    "\n\nEmit only one syntactically valid TLA+ module. Follow this exact top-level "
    "contract and do not invent other keywords: module header; CONSTANTS; VARIABLES; "
    "named definitions Init, Next, and one invariant/property; PROPERTIES. "
    "Use 'Init ==' and 'Next ==' as definitions, never 'SPECIFICATION Init ==' or "
    "'SPECIFICATION Next =='. Use SPECIFICATION only once, on a line by itself, "
    "followed by '    Init /\\\\ Next'. Use PROPERTIES only for named property "
    "identifiers. TLA+ has no semicolons, ':=', FI/OD, or imperative FOR loops: use "
    "LET/IN, IF/THEN/ELSE, and /\\\\. Separate every top-level definition with a "
    "blank real newline. Keep the module short and stop after the final property. "
    "Return no markdown, prose, or escaped newlines."
)
DEFINITION_BOUNDARY_SUFFIX = (
    "\n\nRewrite the answer into a minimal valid TLA+ module before emitting it. "
    "Treat every top-level declaration as a complete unit: one identifier per "
    "VARIABLES line, then a blank line, then each named definition ending at "
    "the newline before the next definition or section. Never continue a "
    "declaration with an expression token such as LET, IF, or <. Do not put "
    "type annotations after values, and do not use pseudo-code. The only "
    "top-level sections are MODULE, CONSTANTS, VARIABLES, definitions, "
    "SPECIFICATION, and PROPERTIES. Use valid TLA+ operators (\\in, /\\, \\\\in, "
    "==, <>) and emit exactly one short Init and one short Next. Return only "
    "the module, with real newlines and no markdown or prose."
)
OUTPUT_TEMPLATE_SUFFIX = (
    "\n\nUse this exact output layout and nothing else: first `---- MODULE <name> ----`, "
    "then one VARIABLES identifier per line, then complete definitions in separate "
    "blocks, then `====` as the final line. Do not write a declaration keyword inside "
    "a definition. Every definition must use `Name == expression` on one line, with "
    "continuation lines indented until the next blank line. For set mappings always "
    "write `[x \\in S |-> expr]`; for sequence values write `<<x>>` without a type "
    "annotation. Use only `LET ... IN ...`, `IF ... THEN ... ELSE ...`, and `/\\` "
    "for compound expressions. Emit a short module, exactly one Init and one Next, "
    "and no prose, markdown fences, or escaped newlines."
)
DECLARATION_COMMAS_SUFFIX = (
    "\n\nEmit one complete TLA+ module and make declarations parseable before "
    "writing any definitions. In a VARIABLES declaration, put all variable "
    "identifiers on one line separated by commas, for example `VARIABLES a, b, c`; "
    "do not place one bare identifier per line. Keep CONSTANTS and VARIABLES "
    "outside every definition. Write `Init == ...` and `Next == ...` as named "
    "definitions, then use `SPECIFICATION == Init /\\\\ Next` and a separate "
    "`PROPERTIES` section. Use only TLA+ operators (`\\in`, `==`, `/\\`, `IF/THEN/ELSE`, "
    "and `LET/IN`), no assignment syntax or imperative loops. Return only plain "
    "TLA+ with one final `====` line and no prose or markdown."
)
CANONICAL_SYNTAX_SUFFIX = (
    "\n\nEmit one complete TLA+ module using this exact legal skeleton: "
    "`---- MODULE <name> ----`, CONSTANTS, VARIABLES, `Init == ...`, "
    "`Next == ...`, `====`. Do not emit a `SPECIFICATION` or `PROPERTIES` "
    "section. In every set/function mapping write `[x \\in S |-> expr]` "
    "with the literal TLA+ operator `\\in`, never `IN`. Use `=` for state "
    "predicates and `==` only after a definition name; never write "
    "`SPECIFICATION ==`. Keep `Init` and `Next` short, with valid LET/IN "
    "expressions and real newlines. Return only plain TLA+ and no prose, "
    "markdown fences, escaped newlines, or pseudo-code."
)
LET_BOUNDARY_SUFFIX = (
    "\n\nUse only canonical TLA+ expression syntax. Every `LET` must contain one "
    "or more named definitions, each ending with `==` and separated by real "
    "newlines, followed by exactly one `IN` expression; never use semicolons, "
    "commas, assignment syntax, or adjacent definitions without `==`. Keep "
    "compound expressions joined with `/\\`, and put each operator on its own "
    "syntactic line. Do not place `LET` inside a declaration or between a name "
    "and its definition. Return one short complete module with only legal TLA+ "
    "and a final `====` line, with no prose or markdown."
)
MODULE_BODY_SCHEMA_SUFFIX = (
    "\n\nBefore emitting, rewrite the answer to this exact module-body shape: "
    "`---- MODULE Name ----`, optional `CONSTANTS`, one comma-separated "
    "`VARIABLES` declaration, then only named definitions `Init == ...`, "
    "`Next == ...`, and one invariant definition. Each definition must be "
    "complete and closed before the next blank line or keyword. Put all "
    "expression-level LET/IF/sequence terms inside Init or Next; never put "
    "EVALUATE, LET, or a sequence expression between top-level declarations. "
    "After the definitions, write exactly one `SPECIFICATION` line followed by "
    "`Init /\\\\ Next`, then optional `INVARIANTS`/`PROPERTIES`, and finish "
    "immediately with `====`. Do not repeat SPECIFICATION, do not append any "
    "alternative module, and return only plain TLA+ with real newlines."
)
STRICT_MODULE_SYNTAX_SUFFIX = (
    "\n\nEmit one minimal TLA+ module and obey these parser-critical rules literally: "
    "write exactly one `VARIABLES a, b, c` line with comma-separated names and "
    "never put a bare variable name on a following line. Every `LET` must be "
    "`LET name == expression` followed by `IN expression`; if several names are "
    "needed, give each its own `==` definition on a separate line. Never write "
    "a bare `LET` name, assignment syntax, imperative FOR, semicolons, or a "
    "declaration keyword inside an expression. Use only `Init ==`, `Next ==`, "
    "one invariant, one `SPECIFICATION` line, and `Init /\\ Next`; finish with "
    "`====`. Return only plain TLA+ with real newlines and no markdown or prose."
)
LET_DEFINITION_OPERATOR_SUFFIX = (
    "\n\nThe previous draft must be rewritten before you finish. In TLA+, a LET "
    "binding is never `LET name =` and never nests another LET immediately after "
    "a bare name. Use this exact form every time: `LET name == expression IN "
    "body`. For multiple bindings, use `LET first == expression` on one line, "
    "then `second == expression` on the next line, then `IN body`; do not write "
    "another LET between those lines. Keep all bindings inside Init or Next, "
    "and close the expression before the next top-level definition. Emit one "
    "minimal module with `VARIABLES a, b, c`, exactly one Init, one Next, one "
    "SPECIFICATION line, and a final `====`. No prose, pseudo-code, assignment, "
    "or second module."
)

def sha(value):
    if isinstance(value, str): value = value.encode()
    return hashlib.sha256(value).hexdigest()

def load_receipt(path):
    r = json.loads(Path(path).read_text())
    if not str(r.get("status", "")).startswith("inputs_recovered") or r["budget"] != {
        "rows": [47, 107], "generations_per_row": 2,
        "arms": ["existing_decoder", "grammar_enforced"],
        "max_new_tokens": 1024, "item_seconds": 45,
        "sany_seconds": 30, "seed": 20261011,
        "parameter_updates": 0, "gate_claim": False}:
        raise ValueError("unexpected or non-frozen protected experiment receipt")
    return r

def post(base, body, timeout):
    req = Request(base.rstrip("/") + "/chat/completions",
                  data=json.dumps(body).encode(),
                  headers={"content-type": "application/json",
                           "Authorization": "Bearer " + os.environ.get("OPENAI_API_KEY", "dummy")})
    with urlopen(req, timeout=timeout) as response:
        return json.loads(response.read())

REQUEST_TIMEOUT_SECONDS = 180

def run(args):
    prompt_intervention = getattr(args, "prompt_intervention", "none")
    out = Path(args.output)
    if out.exists(): raise ValueError("append-only output already exists")
    frozen = load_receipt(args.input_receipt)
    packet_bytes = Path(args.packet).read_bytes()
    if sha(packet_bytes) != frozen["packet"]["sha256"]:
        raise ValueError("packet hash does not match recovered receipt")
    # The Sophia inference environment contains an unrelated site-package named
    # ``tools``.  Keep this frozen runner self-contained at the transport
    # boundary instead of relying on a project checkout or import-path order.
    packet_tools = sys.modules.get("tools.proof_fullmodule_multiexample_probe")
    if packet_tools is not None:
        selected, packet = packet_tools.selected(packet_bytes)
    else:
        packet = json.loads(packet_bytes)
        rows, encodings = packet.get("rows"), packet.get("encodings")
        if not isinstance(rows, list) or not isinstance(encodings, list) or len(rows) != len(encodings):
            raise ValueError("frozen packet rows/encodings are malformed")
        wanted = {47: "w4-fullmodule:w4opus::d2-m7-p4-t2", 107: "w4-fullmodule:w4opus::d3-m0-p0-t0"}
        selected = {}
        for row_number, wanted_id in wanted.items():
            matches = [(row, enc) for row, enc in zip(rows, encodings) if row.get("id") == wanted_id]
            if len(matches) != 1:
                raise ValueError(f"frozen packet row {row_number} is missing or duplicated")
            selected[row_number] = matches[0]
    grammar = Path(args.grammar).read_text() if args.grammar else None
    out.mkdir(parents=True)
    records = []
    for row in ROWS:
        prompt = selected[row][0]["prompt"]
        if sha(prompt) != frozen["rows"][str(row)]["prompt_sha256"]:
            raise ValueError("packet prompt hash does not match recovered receipt")
        base_prompt_sha256 = sha(prompt)
        if prompt_intervention == "syntax_repair":
            prompt = prompt + SYNTAX_REPAIR_SUFFIX
        elif prompt_intervention == "structural_repair":
            prompt = prompt + STRUCTURAL_REPAIR_SUFFIX
        elif prompt_intervention == "declaration_schema":
            prompt = prompt + DECLARATION_SCHEMA_SUFFIX
        elif prompt_intervention == "separator_aware":
            prompt = prompt + SEPARATOR_AWARE_SUFFIX
        elif prompt_intervention == "compact_module":
            prompt = prompt + COMPACT_MODULE_SUFFIX
        elif prompt_intervention == "section_contract":
            prompt = prompt + SECTION_CONTRACT_SUFFIX
        elif prompt_intervention == "definition_boundary":
            prompt = prompt + DEFINITION_BOUNDARY_SUFFIX
        elif prompt_intervention == "output_template":
            prompt = prompt + OUTPUT_TEMPLATE_SUFFIX
        elif prompt_intervention == "declaration_commas":
            prompt = prompt + DECLARATION_COMMAS_SUFFIX
        elif prompt_intervention == "canonical_syntax":
            prompt = prompt + CANONICAL_SYNTAX_SUFFIX
        elif prompt_intervention == "let_boundary":
            prompt = prompt + LET_BOUNDARY_SUFFIX
        elif prompt_intervention == "module_body_schema":
            prompt = prompt + MODULE_BODY_SCHEMA_SUFFIX
        elif prompt_intervention == "strict_module_syntax":
            prompt = prompt + STRICT_MODULE_SYNTAX_SUFFIX
        elif prompt_intervention == "let_definition_operator":
            prompt = prompt + LET_DEFINITION_OPERATOR_SUFFIX
        for arm in ARMS:
            for generation in range(2):
                body = {"model": args.model, "messages": [{"role":"user", "content": prompt}],
                        "max_tokens": 1024, "temperature": 0.0,
                        "seed": 20261011 + generation}
                if arm == "grammar_enforced":
                    if not grammar: raise ValueError("grammar arm requires --grammar")
                    # vLLM 0.22 accepts the legacy field but silently ignores it.
                    # Use the structured-output transport that is actually
                    # enforced by the audited serving interface.
                    body["structured_outputs"] = {"grammar": grammar}
                started = time.time()
                # The frozen 45-second item budget governs the generation
                # request, but vLLM can deliver a full 1024-token response
                # slightly after that boundary when the model is cold or a
                # structured-output kernel JIT-compiles.  Keep the request
                # alive long enough to collect the bounded response instead
                # of misclassifying a completed inference as launcher loss.
                response = post(args.base_url, body, REQUEST_TIMEOUT_SECONDS)
                choice = (response.get("choices") or [{}])[0]
                message = choice.get("message") or {}
                text = message.get("content") or ""
                records.append({"row": row, "arm": arm, "generation": generation,
                    "request_sha256": sha(json.dumps(body, sort_keys=True)),
                    "raw_reply": text, "raw_reply_sha256": sha(text),
                    "finish_reason": choice.get("finish_reason"),
                    "elapsed_seconds": time.time() - started,
                    "response": response, "base_prompt_sha256": base_prompt_sha256,
                    "prompt_intervention": prompt_intervention})
    receipt = {"schema": 1, "kind": "protected_paired_inference",
               "complete": len(records) == 8, "rows": list(ROWS), "arms": list(ARMS),
               "generations_per_row": 2, "parameter_updates": 0,
               "input_receipt": str(Path(args.input_receipt).resolve()),
               "packet_sha256": frozen["packet"]["sha256"],
               "grammar_sha256": sha(grammar) if grammar else None,
               "prompt_intervention": prompt_intervention,
               "records": records, "gate_claim": False}
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--input-receipt", required=True)
    p.add_argument("--packet", required=True)
    p.add_argument("--base-url", default=os.environ.get("OPENAI_BASE_URL"), required=False)
    p.add_argument("--model", required=True)
    p.add_argument("--grammar")
    p.add_argument("--output", required=True)
    p.add_argument("--prompt-intervention", choices=("none", "syntax_repair", "structural_repair", "declaration_schema", "separator_aware", "compact_module", "section_contract", "definition_boundary", "output_template", "declaration_commas", "canonical_syntax", "let_boundary", "module_body_schema", "strict_module_syntax", "let_definition_operator"), default="none")
    a = p.parse_args()
    if not a.base_url: p.error("--base-url or OPENAI_BASE_URL is required")
    run(a)
