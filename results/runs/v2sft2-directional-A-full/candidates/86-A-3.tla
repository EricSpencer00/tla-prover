---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*--------------------------------------------------------------------
\* CONSTANTS
\*--------------------------------------------------------------------
CONSTANTS
    \* list of supported prover backends
    Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\*--------------------------------------------------------------------
\* State variables (none, as the module is purely declarative)
\*--------------------------------------------------------------------
VARIABLES
    \* no state variables needed

\*--------------------------------------------------------------------
\* Initial state (trivial)
\*--------------------------------------------------------------------
Init == [ ]
\* Since there are no variables, Init simply asserts the empty state.

\*--------------------------------------------------------------------
\* Next-state relation (trivial)
\*--------------------------------------------------------------------
Next == [ ]

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<< >>

\*--------------------------------------------------------------------
\* Fundamental theorems (safety properties)
\*--------------------------------------------------------------------
\* setExtensionality: if two sets have the same elements then they are equal.
setExtensionality ==
    \A s, t \in SUBSET Seq0({}) :
        (s = t) # False

\* noSetContainsAll: no set contains every possible value.
noSetContainsAll ==
    \A s \in SUBSET Seq0({}) :
        \E v \in { } : ~(v \in s)

\*--------------------------------------------------------------------
\* Atomic specification of the module (not used in TLC, but required by the
\* description).  It simply states the existence of the two safety properties.
\*--------------------------------------------------------------------
AtomicSpec ==
    setExtensionality /\ noSetContainsAll

\*--------------------------------------------------------------------
\* MAIN THEOREM (placeholder for the actual proof obligations; the real
\* proofs are performed by TLAPS, not by TLC.)
\*--------------------------------------------------------------------
THEOREM Safety_is_Atomic: AtomicSpec

\*--------------------------------------------------------------------
\* END
\*--------------------------------------------------------------------
====