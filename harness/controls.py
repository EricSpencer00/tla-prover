"""Vacuity/control battery (W0.4): known-flawed specs that MUST fail as designed.

Run: python3 -m harness.controls   -> exit 0 only if every control behaves as designed.
"""
import shutil
import sys
from pathlib import Path

from .runner import check_sany, check_tlc

CONTROLS_DIR = Path(__file__).parent / "controls"
CFGS = {
    "BadInv": "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    "DeadEnd": "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    "Vacuous": "INIT Init\nNEXT Next\n",  # deliberately no invariant
    "TrueInv": "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    "UnreachableNext": "INIT Init\nNEXT Next\nINVARIANT Inv\n",
}
# control -> (expected sany, expected tlc, must_be_flagged_vacuous)
EXPECT = {
    "BadParse": ("fail", None, False),
    "BadInv": ("pass", "fail_invariant", False),
    "DeadEnd": ("pass", "fail_deadlock", False),
    "Vacuous": ("pass", "pass", True),  # passes TLC but MUST trip vacuity flags
    # real state changes, real invariant name in cfg, but Inv == TRUE: MUST trip
    # the static trivial-invariant detector (W0.4)
    "TrueInv": ("pass", "pass", True),
    # Next's guard is self-contradictory, never enabled even from Init: MUST
    # deadlock immediately (W0.4's "unreachable-Next", the same detection path
    # as DeadEnd but with zero reachable successors instead of two)
    "UnreachableNext": ("pass", "fail_deadlock", False),
}


def main():
    work = Path("/tmp/prove-tla-controls")
    if work.exists():
        shutil.rmtree(work)
    failures = []
    for name, (exp_sany, exp_tlc, exp_vac) in EXPECT.items():
        wd = work / name
        wd.mkdir(parents=True)
        shutil.copy(CONTROLS_DIR / f"{name}.tla", wd / f"{name}.tla")
        sany, _, _ = check_sany(wd / f"{name}.tla", wd, 60)
        ok = sany == exp_sany
        tlc = vac = None
        if ok and exp_tlc is not None:
            cfg_text = CFGS[name]
            (wd / f"{name}.cfg").write_text(cfg_text)
            tlc, vac, _, _ = check_tlc(name, cfg_text, wd, 60)
            ok = tlc == exp_tlc and (bool(vac) == exp_vac)
        verdict = "OK " if ok else "FAIL"
        print(f"[{verdict}] {name:<9} sany={sany} (want {exp_sany})  "
              f"tlc={tlc} (want {exp_tlc})  vacuity_flags={vac} (flagged wanted: {exp_vac})")
        if not ok:
            failures.append(name)
    shutil.rmtree(work, ignore_errors=True)
    if failures:
        print(f"\nCONTROL BATTERY FAILED: {failures} — the harness cannot be trusted (Gate 0 blocked).")
        sys.exit(1)
    print("\nControl battery passed: every flawed spec fails exactly as designed.")


main()
