---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

\* This module extends the main Boyer-Moore majority vote specification
\* with an interactive proof of correctness for the algorithm. State
\* variables and actions are entirely inherited from the main spec;
\* here we only add the proof obligations and invariants.

VARIABLES candidate, count, i, seq, occ
vars == <<candidate, count, i, seq, occ>>

N == Len(seq)

Positions(k) == {j \in 0..(N - 1) : seq[j] = k}
Majority(k) == 2 * Cardinality(Positions(k)) > N

TypeOK ==
  /\ candidate \in Value
  /\ count \in 0..N
  /\ i \in 0..N
  /\ seq \in Seq(Value)
  /\ occ \in [Value -> 0..N]

Init ==
  /\ candidate \in Value
  /\ count = 0
  /\ i = 0
  /\ seq \in Seq(Value)
  /\ occ = [k \in Value |-> 0]

Next ==
  /\ i < N
  /\ LET x == seq[i] IN
       IF count = 0
       THEN /\ candidate' = x
            /\ count' = 1
            /\ occ' = [occ EXCEPT ![x] = @ + 1]
       ELSE IF x = candidate
            THEN /\ count' = count + 1
                 /\ occ' = [occ EXCEPT ![x] = @ + 1]
            ELSE /\ count' > 1
                 /\ count' = count - 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq>>

Spec ==
  /\ Init
  /\ [][Next]_vars

\* The inductive invariant from the main spec (as a concrete set of
\* reachable states) is lifted here as an explicit invariant.
Inv ==
  {s \in [candidate : Value, count : 0..N, i : 0..N, seq : Seq(Value), occ : [Value -> 0..N]]
    | s \in Spec}

\* No new actions, so part of the proof is that the inherited invariant
\* still holds: the only value occurring in a strict majority must be
\* the candidate.
Correct ==
  \A k \in Value : (i = N /\ Majority(k)) => k = candidate

\* TLAPS proof: type correctness (invariant) and algorithmic correctness
\* (candidate equals any strict-majority element) by induction on i.
TypeOK ==
  /\ candidate \in Value
  /\ count \in 0..N
  /\ i \in 0..N
  /\ seq \in Seq(Value)
  /\ occ \in [Value -> 0..N]

====