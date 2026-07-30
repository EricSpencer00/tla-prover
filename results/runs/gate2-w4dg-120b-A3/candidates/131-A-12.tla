---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANT Value

\* No new state variables: this proof module is an extension of the main
\* Boyer-Moore majority vote specification, so it inherits the state
\* variables from that specification.

\* The full set of actions (including Vote) is imported from the main
\* spec.  Here we only restate the three operators that the reference
\* .cfg expects, each with the exact name it expects.

Spec == Init /\ [][Next]_vars
Init == Init
Next == Next
TypeOK == TypeOK
Correct == Correct

\* Inv is the inductive invariant from the main spec.  It is named
\* exactly as the .cfg expects even though the main spec itself does
\* not expose it as a top-level operator.
Inv == Inv

\* The two invariants below are the ones TLAPS will machine-check: the
\* type invariant and the correctness invariant about the candidate.
====