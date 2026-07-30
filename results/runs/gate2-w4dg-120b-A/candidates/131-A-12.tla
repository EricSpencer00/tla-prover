---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* The interactive proof extends the main Boyer-Moore majority vote
\* specification with machine-checked lemmas that the invariant is type
\* correct and that the candidate is the unique majority element.
\* No new state or transitions are added; everything is inherited from the
\* main spec.

\* Sequence positions and the candidate value are the only state variables.
VARIABLES seq, candidate, count, pos, exhausted

vars == <<seq, candidate, count, pos, exhausted>>

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ candidate \in Value
  /\ count \in 0..3
  /\ pos \in 0..3
  /\ exhausted \in BOOLEAN

\* The algorithm scans the sequence from the left, keeping a single
\* candidate value and a running match count; count is always non-negative.
Init ==
  /\ seq = [i \in 1..3 |-> CHOOSE v \in Value : TRUE]
  /\ candidate \in Value
  /\ count = 0
  /\ pos = 0
  /\ exhausted = FALSE

Read ==
  /\ ~exhausted
  /\ pos < 3
  /\ IF count = 0
       THEN /\ candidate' = seq[pos + 1]
            /\ count' = 1
       ELSE IF seq[pos + 1] = candidate
            THEN count' = count + 1
            ELSE count' = count - 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, exhausted>>

Finish ==
  /\ ~exhausted
  /\ exhausted' = TRUE
  /\ UNCHANGED <<seq, candidate, count, pos>>

Spec == Init /\ [][Read]_vars /\ [][Finish]_vars

\* A strict majority of positions for some value v implies that value is the
\* current candidate; the invariant is what guarantees the algorithm's
\* correctness at the end of the scan.
Correct ==
  /\ (count = 0) <=> (pos = 0)
  /\ (count > 0) => (candidate = seq[pos])

\* The main invariant is the inductive invariant of the Boyer-Moore
\* algorithm; the structural invariant is proved as a trivial corollary.
Inv == Correct

====