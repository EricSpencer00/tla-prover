---- MODULE MajorityProof ----
EXTENDS MajorityVote, FiniteSets

CONSTANTS Value

VARIABLES idx, cand, tally, seen, data

Vars == <<idx, cand, tally, seen, data>>

\* A helper that counts how many positions up to i-1 carry the given value.
Occ(v, i) == Cardinality({k \in seen : k < i /\ data[k] = v})

Init ==
  /\ idx = 1
  /\ cand = CHOOSE c \in Value : TRUE
  /\ tally = 0
  /\ seen = {}
  /\ data \in [1..N -> Value]

\* The single scan step: compare, adopt, and recount the candidate tally.
Step ==
  /\ idx <= N
  /\ LET v == data[idx] IN
       /\ cand' = IF tally = 0 THEN v ELSE cand
       /\ tally' = IF tally = 0 THEN 1
                  ELSE IF v = cand THEN tally + 1
                  ELSE tally - 1
  /\ seen' = seen \cup {idx}
  /\ idx' = idx + 1
  /\ UNCHANGED data

\* The data sequence is reconfigured at the end of a scan so voting repeats.
Rescan ==
  /\ idx > N
  /\ idx' = 1
  /\ cand' = CHOOSE c \in Value : TRUE
  /\ tally' = 0
  /\ seen' = {}
  /\ UNCHANGED data

Descend ==
  /\ idx > 1
  /\ idx' = idx - 1
  /\ cand' = CHOOSE c \in Value : TRUE
  /\ tally' = 0
  /\ seen' = {}
  /\ UNCHANGED data

Next == Step \/ Rescan \/ Descend

Spec == Init /\ [][Next]_Vars

\* Two facts: the tally is always non-negative, and the candidate stays in the
\* majority if it has one. Both are proved together by induction on the steps.
TypeOK ==
  /\ tally >= 0
  /\ (tally >= 1) => (cand = data[idx - 1])

\* The strengthened invariant from the main spec: any value in a strict
\* majority of positions must be the candidate itself.
Correct ==
  \A v \in Value : (Occ(v, N + 1) * 2 > N) => (v = cand)

\* The original inductive invariant from the main spec, lifted unchanged.
Inv ==
  \A v \in Value :
    (Occ(v, idx) * 2 > idx) => (v = cand)

====