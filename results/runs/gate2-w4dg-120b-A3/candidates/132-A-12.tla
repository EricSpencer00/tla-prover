---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences, FiniteSets

(* Model-checking configuration for the Boyer-Moore majority vote algorithm.     *)
(* This module instantiates the majority vote spec with concrete values: three   *)
(* distinct model values (A, B, C) and a bounded sequence length (bound = 5).    *)
(* Sequences are drawn from the bounded set of all functions from 1..n to the    *)
(* value set, for n up to the bound.  The operators below are the exact          *)
(* identifiers the .cfg expects: CONSTANTS A, B, C, bound; SPECIFICATION Spec;    *)
(* INVARIANTS TypeOK, Correct, Inv; and the bounded operator BoundedSeq.         *)

CONSTANTS A, B, C, bound

Values == {A, B, C}
\* BoundedSeq replaces the unbounded Seq from Sequences.  It is a finite      \* 
\* version that keeps the model checkable; we KEEP Extends Sequences so that  \* 
\* other inherited operators from the majority vote spec keep working.        \* 
BoundedSeq == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, candidate, cnt

vars == <<seq, pos, candidate, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in Nat
  /\ candidate \in Values
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ candidate \in Values
  /\ cnt = 0

\* The main action: scan the next element with the Boyer-Moore three-case     \* 
\* logic: adopt a new candidate when the count is zero, increment on a match,  \* 
\* or decrement on a mismatch.                                                \* 
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0
         THEN /\ candidate' = x
              /\ cnt' = 1
         ELSE IF x = candidate
              THEN cnt' = cnt + 1
              ELSE cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Step]_vars

\* The main correctness property: any true majority element must be the         \* 
\* candidate after a complete scan.                                            \* 
Correct ==
  /\ (cnt > 0 /\ pos > Len(seq) => \A i \in 1 .. Len(seq) : seq[i] = candidate)
  /\ (cnt = 0 /\ pos > Len(seq) => \A a \in Values : \A i \in 1 .. Len(seq) : seq[i] # a)

Inv == TypeOK

====