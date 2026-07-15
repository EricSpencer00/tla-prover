---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Configuration constants (no actors, used only as placeholders)
\* ----------------------------------------------------------------------
CONSTANTS
    timeouts,            \* map from backend name to timeout (seconds)
    tactics,            \* map from backend name to tactic description
    backends            \* set of backend prover names

\* ----------------------------------------------------------------------
\* Backend configuration defaults (can be overridden in .cfg)
\* ----------------------------------------------------------------------
timeouts == [zenon |-> 5,
             isabelle |-> 10,
             cvc3 |-> 5,
             yices |-> 5,
             veriT |-> 5,
             Z3 |-> 5,
             spass |-> 5,
             LS4 |-> 10]

tactics == [zenon |-> "default",
            isabelle |-> "default",
            cvc3 |-> "default",
            yices |-> "default",
            veriT |-> "default",
            Z3 |-> "default",
            spass |-> "default",
            LS4 |-> "default"]

backends == {"zenon", "isabelle", "cvc3", "yices",
             "veriT", "Z3", "spass", "LS4"}

\* ----------------------------------------------------------------------
\* The minimal state (empty) – the module has no runtime state
\* ----------------------------------------------------------------------
VARIABLES dummy

\* No real state, dummy is always 0
InitDummy == dummy = 0

\* ----------------------------------------------------------------------
\* Specification components required by the cfg (even though they are
\* vacuous for this configuration‑only module)
\* ----------------------------------------------------------------------
Specification == Init /\ [][][Next]_vars

Init == InitDummy

Next == UNCHANGED dummy

\* No invariants or external properties are defined in the description,
\* but the identifiers must exist.
\* ----------------------------------------------------------------------
INVARIANTS == {}

PROPERTIES == {}

\* ----------------------------------------------------------------------
\* Backend dispatch operators – they do not affect the model state;
\* they merely expose the configuration constants.
\* ----------------------------------------------------------------------
BackendTimeout(p) == timeouts[p]
BackendTactic(p)   == tactics[p]

\* ----------------------------------------------------------------------
\* Temporal logic proof rule placeholders (names only, no implementation)
\* ----------------------------------------------------------------------
InvRule == "InvRule placeholder"
WellFormedRule == "WellFormedRule placeholder"
StrongFairnessRule == "StrongFairnessRule placeholder"
WeakFairnessRule == "WeakFairnessRule placeholder"
StepSimulationRule == "StepSimulationRule placeholder"

\* ----------------------------------------------------------------------
\* Core theorems mentioned in the description
\* ----------------------------------------------------------------------
SetExtensionality == \A A, B \in SUBSET Universe :
                     (\A x \in Universe : x \in A <=> x \in B) => A = B

NoUniversalSet == \A S \in SUBSET Universe : \E x \in Universe : x \notin S

\* The universe of discourse – all possible values
Universe == Nat \cup {"foo", "bar", "baz"}

\* ----------------------------------------------------------------------
\* THEOREMS (named as required)
\* ----------------------------------------------------------------------
THEOREM SetExtensionality
THEOREM NoUniversalSet

====