---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  None

\* Provers for the proof infrastructure are declared as constants, so no new one
\* can be introduced by a later spec revision without changing this module.
Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4 == None

\* Which operators to invoke in each layer of TLAPS' dispatch hierarchy.
\* The first non-None prover in the list is the one that actually gets called.
Tactics ==
  <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4>>

\* Operators that the proof system's build system looks for by exact name:
\*   SPECIFICATION, INIT, NEXT, INVARIANTS, PROPERTIES
\* Leaving any of these out, or renaming them, makes the spec un-runnable.
SPECIFICATION == Init /\ [][Next]_none
Init == TRUE
Next == TRUE

INVARIANTS == {Extensionality, Boundedness}
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B
Boundedness == \A S \in SUBSET Nat : ~(\A x \in Nat : x \in S)

PROPERTIES == {}

\* Prover-dispatch operator: given a proof goal, the first prover in Tactics
\* that is not None is the one TLAPS calls on it.
Dispatch(g) == CHOOSE p \in Tactics : p # None

====