---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

VARIABLES cand, cnt, i, seq

(*-----------------------------------------------------------------------
  Helper definitions
  -----------------------------------------------------------------------*)
Cand(i) == cand[i]
Cnt(i) == cnt[i]

(*-----------------------------------------------------------------------
  Types
  -----------------------------------------------------------------------*)
TypeOK == 
    /\ cand \in [0..Len(seq) -> Value \cup {"null"}]
    /\ cnt \in [0..Len(seq) -> Nat]
    /\ i \in 0..Len(seq)
    /\ seq \in Seq(Value)

(*-----------------------------------------------------------------------
  Specification (from the original Boyer-Moore algorithm)
  -----------------------------------------------------------------------*)
Init ==
    /\ i = 0
    /\ cand = [j \in 0..Len(seq) |-> "null"]
    /\ cnt = [j \in 0..Len(seq) |-> 0]

Next ==
    \/ /\ i < Len(seq)
       /\ LET x == seq[i+1] IN
          IF cnt[i] = 0 THEN
              /\ cand' = [cand EXCEPT ![i+1] = x]
              /\ cnt'  = [cnt  EXCEPT ![i+1] = 1]
          ELSE
              /\ cand' = [cand EXCEPT ![i+1] = cand[i]]
              /\ IF cand[i] = x THEN
                     cnt' = [cnt EXCEPT ![i+1] = cnt[i] + 1]
                 ELSE
                     cnt' = [cnt EXCEPT ![i+1] = cnt[i] - 1]
          /\ i' = i + 1
    \/ /\ i = Len(seq) /\ UNCHANGED <<cand, cnt, i, seq>>

Spec == Init /\ [][Next]_<<cand, cnt, i, seq>>

(*-----------------------------------------------------------------------
  Invariant Inv (the inductive invariant from the main specification)
  -----------------------------------------------------------------------*)
Inv ==
    /\ i \in 0..Len(seq)
    /\ cnt[i] >= 0
    /\ (cnt[i] = 0 => cand[i] = "null")
    /\ (cnt[i] > 0 => cand[i] \in Value)

(*-----------------------------------------------------------------------
  Correctness property: after processing the whole sequence, any strict
  majority element equals the final candidate.
  -----------------------------------------------------------------------*)
StrictMajority(v) == 
    /\ v \in Value
    /\ 2 * Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq)

Correct == 
    \A v \in Value :
        StrictMajority(v) => cand[Len(seq)] = v

====