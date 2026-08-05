---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Vals == {A, B, C}
NONE == 0
Seqs == UNION { [1..n -> Vals] : n \in 0..bound }

VARIABLES seq, i, cand, count

vars == <<seq, i, cand, count>>

TypeOK ==
  /\ seq \in Seqs
  /\ i \in 1..(bound + 1)
  /\ cand \in Vals \cup {NONE}
  /\ count \in 0..bound

Init ==
  /\ seq \in Seqs
  /\ i = 1
  /\ cand \in Vals \cup {NONE}
  /\ count = 0

Step ==
  /\ i <= Len(seq)
  /\ LET x == seq[i] IN
       \/ /\ count = 0
          /\ cand' = x
          /\ count' = 1
       \/ /\ cand = x
          /\ count' = count + 1
          /\ UNCHANGED cand
       \/ /\ cand # x
          /\ count' > 0
          /\ count' = count - 1
          /\ UNCHANGED cand
  /\ i' = i + 1

Complete ==
  /\ i = Len(seq) + 1
  /\ UNCHANGED <<seq, i, cand, count>>

Next == Step \/ Complete

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next) /\ WF_vars(Complete)

Correct ==
  ( \A e \in Vals : (2 * Cardinality({k \in 1..Len(seq) : seq[k] = e}) > Len(seq)) => (cand = e) )
  \/ ( i = Len(seq) + 1 /\ cand # NONE )
  \/ i <= Len(seq)

Inv ==
  ( count > 0 ) => (cand \in Vals)
  /\ ( count > 0 /\ cand = NONE ) => FALSE

AllSteps == (Step)~> (Complete)

====