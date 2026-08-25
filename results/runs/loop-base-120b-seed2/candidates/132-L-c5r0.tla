---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* ----------------------------------------------------------------------
   The three concrete element values
   ---------------------------------------------------------------------- *)
Values == { A, B, C }

(* ----------------------------------------------------------------------
   BoundedSeq replaces the usual Seq definition.
   It contains all (finite) sequences over Values whose length is
   between 0 and bound inclusive.
   ---------------------------------------------------------------------- *)
BoundedSeq ==
  { s \in [Nat -> Values] :
      \E n \in 0..bound :
        ( n = 0 /\ DOMAIN s = {} ) \/
        ( n > 0 /\ DOMAIN s = 1..n )
  }

(* ----------------------------------------------------------------------
   Length of a bounded sequence
   ---------------------------------------------------------------------- *)
Len(s) == IF s = {} THEN 0 ELSE Max(DOMAIN s)

VARIABLES seq, i, cand, cnt

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ seq \in BoundedSeq
  /\ i \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

(* ----------------------------------------------------------------------
   One step of the Boyer‑Moore scan
   ---------------------------------------------------------------------- *)
Next ==
  \/ /\ i <= Len(seq)                \* still elements to scan
     /\ LET x == seq[i] IN
          IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt'  = 1
          ELSIF cand = x THEN
            /\ cand' = cand
            /\ cnt'  = cnt + 1
          ELSE
            /\ cand' = cand
            /\ cnt'  = cnt - 1
        /\ i'   = i + 1
        /\ seq' = seq
  \/ /\ i > Len(seq)                 \* scan finished – stutter
     /\ UNCHANGED <<seq, i, cand, cnt>>

(* ----------------------------------------------------------------------
   The full specification, with weak fairness to guarantee progress
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_<<seq, i, cand, cnt>>(Next)

(* ----------------------------------------------------------------------
   Inductive invariant (here we simply reuse TypeOK)
   ---------------------------------------------------------------------- *)
Inv == TypeOK

(* ----------------------------------------------------------------------
   Correctness property:
   If a value occurs strictly more than half the time in the whole
   sequence, then after the scan finishes the candidate equals that
   value.
   ---------------------------------------------------------------------- *)
Correct ==
  /\ i > Len(seq)                                   \* scan complete
  /\ (\E e \in Values :
        LET n == Len(seq) IN
        Cardinality({ j \in 1..n : seq[j] = e }) > n / 2)
     => (\E e \in Values :
           LET n == Len(seq) IN
           /\ Cardinality({ j \in 1..n : seq[j] = e }) > n / 2
           /\ cand = e)

====