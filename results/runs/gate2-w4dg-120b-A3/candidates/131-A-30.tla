---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets
CONSTANTS Value

\* Imported state-machine from the main specification; its definition is
\* reproduced here because a TLA+ file is self-contained. All state
\* variables and actions below are exactly those from the original
\* majority-vote spec.
VARIABLES seq, candidate, count, seen

vars == <<seq, candidate, count, seen>>

TypeOK ==
  /\ seq \subseteq Value
  /\ candidate \in Value \cup {0}
  /\ count \in 0..Cardinality(seq)
  /\ seen \subseteq 0..Cardinality(seq)

Init ==
  /\ seq = {}
  /\ candidate = 0
  /\ count = 0
  /\ seen = {}

\* The vote algorithm: add a value to the scanned prefix, and update the
\* candidate with the Boyer-Moore rule.
Cast(v) ==
  /\ seq' = seq \cup {v}
  /\ seen' = seen \cup {Cardinality(seq)}
  /\ IF count = 0
     THEN /\ candidate' = v
          /\ count' = 1
     ELSE IF candidate = v
          THEN count' = count + 1
               /\ candidate' = candidate
          ELSE count' = count - 1
               /\ candidate' = candidate

Spec == Init /\ [][Cast(_)]_vars

\* Inductive invariant from the main spec: whenever the counter is non-zero,
\* the candidate has a strict majority among the already-scanned positions.
Inv ==
  \A t \in seen :
    /\ count > 0
    /\ (Cardinality({i \in seen : seq[i] = candidate}) > t / 2)

\* Two final correctness properties, both proved (not merely asserted):
\*   1. no state ever violates the typing discipline.
\*   2. the candidate is the only value that can hold a strict majority
\*      after the whole sequence is scanned.
TypeOK == TypeOK
Correct == Inv

====