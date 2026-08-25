---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The bound is a natural number (concrete value supplied in the .cfg) *)
ASSUME bound \in Nat

(* The set of possible element values *)
Values == { A, B, C }

(* ----------------------------------------------------------------------
   BoundedSeq(S)  –  the set of all finite sequences over S whose length is
   at most the constant *bound*.  It is defined without using the
   (infinite) Seq operator to avoid the infinite enumeration that caused
   the stack overflow.
   ---------------------------------------------------------------------- *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

(* ----------------------------------------------------------------------
   Initial state:
     * seq is any sequence over Values whose length ≤ bound
     * scanning starts at position 1
     * counter is zero
     * candidate is chosen nondeterministically from Values
   ---------------------------------------------------------------------- *)
Init ==
  /\ seq \in BoundedSeq(Values)
  /\ i = 1
  /\ cnt = 0
  /\ cand \in Values

(* ----------------------------------------------------------------------
   One step of the Boyer‑Moore scan.
   When the scan position i is still within the sequence, we examine the
   element seq[i] and update (cand, cnt) according to the classic three‑case
   rule.  Afterwards i is advanced by one.
   When i has already passed the end of the sequence, the state is
   stuttering.
   ---------------------------------------------------------------------- *)
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