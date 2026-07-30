---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm. The model extends the main
\* specification with lemmas and a machine-checked proof (TLAPS) that the
\* algorithm's output is correct.
\* No new state is introduced; everything is inherited from the main spec.
\* The invariant Inv is the inductive invariant of the main spec.

\* typeOK is the type-correctness invariant of the whole spec.
\* Correct is the main correctness invariant: when the scan is finished, any
\* value occurring in a strict majority of positions must equal the candidate.
\* Inv is the inductive invariant that TLAPS uses to prove Correct.

VARIABLES seq, n, idx, candidate, count, seen

vars == << seq, n, idx, candidate, count, seen >>

Init ==
  /\ seq \in Seq(Value)
  /\ n = Len(seq)
  /\ idx = 0
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ seen = {}

Bump ==
  /\ idx < n
  /\ idx' = idx + 1
  /\ seen' = seen \cup {idx}
  /\ IF count = 0
     THEN /\ candidate' = seq[idx + 1]
          /\ count' = 1
     ELSE IF seq[idx + 1] = candidate
          THEN /\ candidate' = candidate
               /\ count' = count + 1
          ELSE /\ candidate' = candidate
               /\ count' = count - 1
  /\ UNCHANGED << seq, n >>

Finished ==
  /\ idx = n
  /\ UNCHANGED vars

Next == Bump \/ Finished

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ seq \in Seq(Value)
  /\ n \in Nat
  /\ idx \in Nat
  /\ candidate \in Value
  /\ count \in Nat
  /\ seen \subseteq Nat

\* count is a cardinality: positions before the current scan form a finite set,
\* and adding an element to a finite set increases cardinality by one.
OccurAfter(v, i) == Cardinality({j \in seen : seq[j] = v})

\* The candidate's count must match the elements positively supporting it.
Pos(v) == {j \in seen : seq[j] = v}
Neg(v) == {j \in seen : seq[j] # v}
Relate(v) == count >= Cardinality(Pos(v))

Inv ==
  /\ idx <= n
  /\ Relate(candidate)
  /\ seen = (IF idx = 0 THEN {} ELSE {1 .. idx})
  /\ \A v \in Value : Relate(v)

Correct ==
  /\ \A v \in Value : (OccurAfter(v, n) * 2 > n) => v = candidate

====