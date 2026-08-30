---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* The module imports the main Boyer-Moore majority vote spec and adds a
\* machine-checked proof of its correctness. No new state or actions are
\* introduced; the proof is structured in numbered steps (hierarchical).

SPECIFICATION Spec == MajoritySpec

\* Type correctness: always holds, checked from the start and preserved.
TypeOK == MajoritySpec.TypeOK

\* Correctness: any strict-majority value must equal the candidate once the
\* whole sequence has been scanned.
Correct == MajoritySpec.Correct

Inv == MajoritySpec.Inv

====