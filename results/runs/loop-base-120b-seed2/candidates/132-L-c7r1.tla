---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* Set of possible values *)
V == { A, B, C }

(* Finite sequences of length at most bound over a set S *)
BoundedSeq(S) == { s \in [Nat -> S] : \E n \in 0..bound : DOMAIN s = 1..n }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq(V)
    /\ i = 1
    /\ cand \in V
    /\ cnt = 0

(* One step of the Boyer‑Moore scan *)
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          /\ IF cnt = 0 THEN
                /\ cand' = x
                /\ cnt' = 1
             ELSE IF cand = x THEN
                /\ cand' = cand
                /\ cnt' = cnt + 1
             ELSE
                /\ cand' = cand
                /\ cnt' = cnt - 1
          /\ i' = i + 1
          /\ UNCHANGED seq
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* Full specification, including weak fairness for progress *)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq(V)
    /\ i \in Nat
    /\ cand \in V
    /\ cnt \in Nat

(* Simple inductive invariant *)
Inv ==
    /\ i \in 1..(Len(seq) + 1)
    /\ cnt \in Nat

(* Definition of a majority element in the current sequence *)
Majority(v) ==
    /\ v \in V
    /\ Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) \div 2

(* Correctness: after a full scan, any true majority must equal the candidate *)
Correct ==
    /\ i = Len(seq) + 1
       => \A v \in V : Majority(v) => cand = v

====