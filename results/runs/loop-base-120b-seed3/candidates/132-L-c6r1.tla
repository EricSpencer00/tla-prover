---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

(* The set of possible element values *)
Values == { A, B, C }

(* Bounded sequences over a set S (length ≤ bound) *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

(* Initial state *)
Init ==
  /\ seq \in BoundedSeq(Values)
  /\ i = 1
  /\ cnt = 0
  /\ cand \in Values

(* One step of the Boyer‑Moore scan *)
Next ==
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
        IF cnt = 0 THEN
          /\ cand' = x
          /\ cnt' = 1
        ELSE IF x = cand THEN
          /\ cand' = cand
          /\ cnt' = cnt + 1
        ELSE
          /\ cand' = cand
          /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i > Len(seq)
     /\ UNCHANGED << seq, i, cand, cnt >>

(* Complete specification *)
Spec == Init /\ [][Next]_vars

(* Type correctness invariant *)
TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ i \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

(* Majority predicate for an element m *)
Majority(m) ==
  Cardinality({ j \in 1..Len(seq) : seq[j] = m }) > Len(seq) \div 2

(* Correctness property: after a full scan, any majority element must equal the candidate *)
Correct ==
  /\ i > Len(seq)
  /\ \A m \in Values : Majority(m) => cand = m

(* Inductive invariant used in the original specification *)
Inv ==
  /\ cnt \in Nat
  /\ cnt <= Len(seq)
  /\ cand \in Values

====