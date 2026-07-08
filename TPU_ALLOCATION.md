# TPU allocation guideline — TRC 6-month grant

Status: draft, 2026-07-06. Grant: **TPU Research Cloud (TRC), 6-month**, per the
`trc-support@google.com` welcome email. This document decides what to reply, what to
request, and how much to actually run — sized to the prove-TLA training workload.

> **All TPU spec numbers below are approximate — verify against the quota menu in the
> TRC *confirmation* email before committing a sweep.** The welcome email is onboarding,
> not the allocation.

---

## 0. What TRC actually gives you (read this first)

- **TRC does not take a "number of TPUs" request up front.** The welcome email wants only
  your **project number** + **owner email**. Reply with those to trigger the grant.
- The quota you get is a **fixed menu**, not a dial. A typical TRC grant is:
  - ~5 on-demand **v2-8**, ~5 on-demand **v3-8**, ~100 **preemptible v2-8** (us-central1-f);
  - **v4 / v5e access on request**, in specific zones (v4: us-central2-b; v5e: us-west/others).
  - *Confirm exact quota in the confirmation email — grants vary.*
- **TRC covers TPU compute only.** You still pay for: Cloud Storage (checkpoints),
  network egress (e.g. pulling/pushing to ALCF), and any non-TPU VMs. Budget for these.
- **The 6-month clock is the binding constraint**, not capacity. Free burst is plentiful;
  calendar time is not. Plan the sweep schedule, not just the machine size.

**Implication for "how much to request":** the default v2-8/v3-8 bundle is **too small to
hold a 21B or 117B MoE** (see §2). The one thing worth explicitly asking for in your reply
is **v4 (and/or v5e) access**. Everything else is about concurrency within the grant.

---

## 1. The workload this has to cover

| Workload | Frequency | Notes |
|---|---|---|
| gpt-oss-20b fine-tune (LoRA → full FT) | primary | the Stage-2 prover-model training the baseline must beat |
| Training sweeps (framings A/B × seeds × HPs) | many small runs | parallelism matters more than single-run size |
| gpt-oss-120b (LoRA-first) | stretch | only after 20b beats the frozen baseline |
| Eval / inference | mostly stays on ALCF/Sophia | could offload some pass@k to TPU if endpoint is cold |

Design principle (project ethos): **measure before you claim.** Right-size from a profiling
run, not a guess; log every run to `results/runs/` with slice type, wall-clock, and $ (Rule 8).

---

## 2. Memory sizing — why model size drives the machine

Rules of thumb (bf16):
- **Full fine-tune (Adam):** ≈ **16 bytes/param** (weights + fp32 master + m + v) + activations.
- **LoRA/PEFT:** ≈ base weights only (**2 B/param** bf16, or ~1 B int8) + small adapter states.

| Model | Params | Full-FT footprint | LoRA footprint | Full-FT fits | LoRA fits |
|---|---|---|---|---|---|
| gpt-oss-20b | ~21B | ~340 GB | ~45 GB | **v4-32** (512 GB) comfortably; v4-16 tight | v4-8 / v3-8 (128 GB) |
| gpt-oss-120b | ~117B | ~1.9 TB | ~240 GB | v4-128 / v4-256 | v4-16 / v4-32 |

HBM per slice (approx): v2-8 ≈ 64 GB · v3-8 ≈ 128 GB · v4-8 ≈ 128 GB · v4-32 ≈ 512 GB ·
v4-64 ≈ 1 TB · v5e-8 ≈ 128 GB.

**Key takeaway:** the free **100× preemptible v2-8** (64 GB) can't even hold the 20b weights
(~42 GB) with room for activations across 8 cores — treat that quota as **mostly unusable for
this project**. The 20b work needs **v4** (or v3-8 for LoRA only). This is the reason to request
v4 access explicitly.

---

## 3. What to reply to the TRC email

Send the two required fields, and in the same reply, ask for v4/v5e:

> Project number: `<all-digits>`
> Project owner: `<email>`
>
> Our workload is fine-tuning Mixture-of-Experts models of ~21B and ~117B parameters. The
> default v2-8/v3-8 quota is too small to hold these. Could we get **v4 access in
> us-central2-b** (and v5e if available), ideally up to a **v4-64 preemptible** slice for
> training sweeps plus a small on-demand slice for interactive development?

Do the prerequisites first: pick/create the GCP project, enable the Cloud TPU API, then reply.

---

## 4. Recommended allocation — three tiers

Request the **Recommended** tier; the others bracket it.

| Tier | Interactive (on-demand) | Training (preemptible) | Covers | When |
|---|---|---|---|---|
| **Minimum viable** | 1× v4-8 (or default v3-8) | 2× v4-8 | 20b **LoRA** only, small sweeps | if v4 quota is limited |
| **Recommended** | 1× v4-8 | 1× v4-32 + 2–4× v4-8 | 20b **full FT** + parallel LoRA sweeps | default plan |
| **Stretch (120b)** | 1× v4-8 | burst 1× v4-64→128 | 120b **LoRA-first**, few runs | only after 20b beats baseline |

Rationale:
- **1× v4-8 on-demand** = always-available box for pipeline bring-up, debugging, and eval —
  not subject to preemption.
- **v4-32 preemptible** = the full-FT 20b workhorse; preemptible because sweeps are
  checkpoint-restartable and free capacity is the point of TRC.
- **2–4× v4-8** = parallel LoRA/HP sweeps — throughput comes from running many small jobs,
  not one big one.
- **120b** stays LoRA-first and gated behind a 20b win, matching the staged-gate discipline
  and directly answering the ChatTLA critique (a LoRA that *does* touch the MoE experts).

---

## 5. Six-month calendar (the real constraint)

| Phase | Window | Machines | Deliverable |
|---|---|---|---|
| Bring-up + profiling | weeks 1–2 | 1× v4-8 | tokens/sec, $/step, ckpt size measured on a 200-step run |
| **Frozen baseline** | weeks 2–4 | ALCF + 1× v4-8 | `corpus/e2c_baseline.json` — the number a retrain must beat |
| 20b LoRA sweeps | months 1–2 | 2–4× v4-8 preempt. | best LoRA config, expert layers included |
| 20b full FT | months 2–4 | 1× v4-32 preempt. | retrained prover; compare vs baseline (audited) |
| 120b stretch | months 4–5 | v4-64 burst | LoRA-only 120b, only if 20b won |
| Re-eval + writeup | month 6 | 1× v4-8 | audited holdout numbers, PLAN amendment |

**Do not run the baseline until it's frozen** — no training run counts before then (per WEEKLY).

---

## 6. Non-TPU cost budget (TRC doesn't cover these)

- **Cloud Storage:** a 20b bf16 checkpoint ≈ 42 GB; a full-FT Adam checkpoint is larger.
  Keep only best + last few; delete stale sweeps. Target < a few hundred GB resident.
- **Egress:** minimize round-trips to ALCF; stage data in GCS in the TPU's region.
- **Orchestration VM:** one small always-on `e2-small` for the sweep controller — cents/hour.
- Expect **low tens of $/month** if disciplined; checkpoint bloat is the main way this balloons.

---

## 7. Guardrails

- **Measure-first:** profile on 1× v4-8 before booking a v4-32 sweep. No blind scaling.
- **Preemptible-first:** default to preemptible; reserve on-demand for the one interactive box.
- **Checkpoint hygiene:** cap retained checkpoints; GC after every sweep.
- **Ledger every run:** slice type, wall-clock, $, tokens — into `results/runs/` (Rule 8).
- **Don't hoard capacity:** request only what fits inside the 6-month window; unused quota is
  wasted grant, and over-requesting v4 can slow approval.

---

## Open decisions (confirm to finalize numbers)

1. **Scope:** 20b only, or reserve 120b burst? (Sets whether we ask for v4-64+.)
2. **Method:** LoRA (fits v4-8, cheap) vs full FT (needs v4-32) as the primary 20b run.
3. **Zone:** default v4 zone is us-central2-b — confirm data/egress path from ALCF is acceptable.
