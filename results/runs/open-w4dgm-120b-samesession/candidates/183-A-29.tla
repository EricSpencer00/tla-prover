---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Dispatchers: each maps a proof obligation to a backend prover with a
\* timeout and, for Isabelle, an optional tactic.
Dispatchers == [tool: {"Zenon", "Isabelle", "CVC3", "Yices", "veriT", "Z3", "SPASS", "LS4"},
                 timeout: Nat, tactic: {"default", "induct", "coherent"}]

IdleDispatch == [tool |-> "Zenon", timeout |-> 10, tactic |-> "default"]

\* Operators are the only required identifiers; there is no state to model.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

\* A given backend is always present in the toolbox, so each of these is
\* always enabled -- never deadlocked, and none can be proven from another.
ExistsZenon == \E d \in Dispatchers : d.tool = "Zenon"
ExistsIsabelle == \E d \in Dispatchers : d.tool = "Isabelle"
ExistsCVC3 == \E d \in Dispatchers : d.tool = "CVC3"
ExistsYices == \E d \in Dispatchers : d.tool = "Yices"
ExistsVeriT == \E d \in Dispatchers : d.tool = "veriT"
ExistsZ3 == \E d \in Dispatchers : d.tool = "Z3"
ExistsSPASS == \E d \in Dispatchers : d.tool = "SPASS"
ExistsLS4 == \E d \in Dispatchers : d.tool = "LS4"

\* TLAPS always has some backend available to hand an obligation to.
NEXT == \/ ExistsZenon \/ ExistsIsabelle \/ ExistsCVC3 \/ ExistsYices
        \/ ExistsVeriT \/ ExistsZ3 \/ ExistsSPASS \/ ExistsLS4

\* Even though these are fundamental theorems rather than system properties,
\* they are placed in the INVARIANTS section so that their names are reserved
\* and cannot clash with any future extension's operator names. Their proofs
\* are external (set theory, arithmetic) and cannot be derived from a dispatch.
INVARIANTS == {Extensionality, UniverseNotFull}

\* The two theorems introduced in the library's opening chapter: set
\* extensionality and the non-existence of a universal set.
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B
UniverseNotFull == \A S \in SUBSET Nat : S # Nat

\* A module presenting no system behavior to verify still has to name at
\* least one liveness property, so the module conservatively asserts the
\* persistence of an always-true fact.
PROPERTIES == {SpecIsNonEmpty}

SpecIsNonEmpty == TRUE

=============================================================================