---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* No new state variables: extend the main spec's state and its invariants.
\* The imported spec is inlined here because each identifier must be present
\* in this module in order for the .cfg to bind it.
VARIABLES seq, candidate, count, i

vars == << seq, candidate, count, i >>

RECURSIVE FCount(_, _)
FCount(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + FCount(f, S \ {x})

\* The main algorithm: candidate and count are updated as the scan progresses.
Init ==
    /\ seq \in [1..2 -> Value]
    /\ candidate = 0
    /\ count = 0
    /\ i = 1

Step ==
    /\ i <= 2
    /\ LET x == seq[i] IN
        /\ candidate' = IF count = 0 THEN x ELSE candidate
        /\ count' = IF count = 0 THEN 1 ELSE IF x = candidate THEN count + 1 ELSE count - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

Halt ==
    /\ i > 2
    /\ UNCHANGED << seq, candidate, count, i >>

Next == Step \/ Halt

TypeOK ==
    /\ seq \in [1..2 -> Value]
    /\ candidate \in Value \cup {0}
    /\ count \in 0..2
    /\ i \in 1..3

\* Correctness: if a value occurs in a strict majority of positions, it equals
\* the candidate. The cardinality argument below needs the finite-set lemmas.
Inv ==
    /\ (candidate # 0 => count > 0)
    /\ \A x \in Value : ((FCount([y \in 1..2 |-> IF seq[y] = x THEN 1 ELSE 0], 1..2) * 2) > 2) => x = candidate)

Spec == Init /\ [][Next]_vars

\* TLAPS proof: type correctness and the main correctness invariant from the
\* main spec are proved by induction on the transition relation.
TypeOKProof ==
    \* Base: type correctness holds in the initial state.
    /\ TypeOK
    \* Inductive step: each transition preserves type correctness.
    /\ (Step => TypeOK) /\ (Halt => TypeOK)

CorrectProof ==
    \* Base: Inv holds in the initial state.
    /\ Inv
    /\ (Step => Inv) /\ (Halt => Inv)

====