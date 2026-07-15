---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

\* ==========================================================================
\* This module models the backend configuration for the TLA Proof System (TLAPS).
\* It defines operators that select which automated provers/backends are to be
\* used for discharging proof obligations, and it includes the two foundational
\* theorems (set extensionality and the non‑triviality of the universe) as
\* invariants.  The specification does not describe any stateful behaviour of
\* a system; it merely provides a vehicle for the configuration constants.
\* ==========================================================================

\*---------------------------------------------------------------------------
\* Backend selection operators (they return the name of the backend to be used
\* for a given proof obligation).  The actual dispatch to the prover is performed
\* by TLAPS; the operators are pure functions of the obligation identifier.
\*---------------------------------------------------------------------------
\* The identifiers below are the exact names required by the reference .cfg.
\*---------------------------------------------------------------------------
Zenon            == "Zenon"
Isabelle         == "Isabelle"
CVC3             == "CVC3"
Yices            == "Yices"
VeriT            == "VeriT"
Z3               == "Z3"
SPASS            == "SPASS"
LS4              == "LS4"

\*---------------------------------------------------------------------------
\* Timeout configuration (in seconds).  These are constants; they can be
\* overridden in a .cfg file if desired.
\*---------------------------------------------------------------------------
ZenonTimeout     == 30
CVC3Timeout      == 60
YicesTimeout     == 30
Z3Timeout        == 30
VeriTTimeout     == 30
SPASSTimeout     == 60
LS4Timeout       == 30

\*---------------------------------------------------------------------------
\* Tactics for the Isabelle backend.  The strings are placeholders for the
\* actual tactic scripts that TLAPS would invoke.
\*---------------------------------------------------------------------------
IsabelleSmtTac    == "smt_solver"
IsabelleReflTac   == "simp"

\*---------------------------------------------------------------------------
\* Theorem: Set extensionality.
\*---------------------------------------------------------------------------
SetExtensionality ==
    \A x \in {A, B} : (x \in A) = (x \in B) => A = B

\*---------------------------------------------------------------------------
\* Theorem: No set contains every possible value (non‑triviality of the universe).
\*---------------------------------------------------------------------------
UniverseNonTrivial ==
    \A S : \E x : x \notin S

\*---------------------------------------------------------------------------
\* Specification of the (trivial) system state.
\*---------------------------------------------------------------------------
VARIABLES dummy

\* The initial state simply sets dummy to 0.
Init ==
    dummy = 0

\* No state‑changing actions; the system stutters forever.
Next ==
    UNCHANGED dummy

\* The overall specification.
Spec ==
    Init /\ [] [Next]_<<dummy>>

\*---------------------------------------------------------------------------
\* Invariants and properties required by the configuration.
\*---------------------------------------------------------------------------
INVARIANTS == { SetExtensionality, UniverseNonTrivial }

\* No additional liveness or temporal properties are defined for this module.
\*---------------------------------------------------------------------------
\* Export the required top‑level operators.
\*---------------------------------------------------------------------------
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next
PROPERTIES    == {}

====