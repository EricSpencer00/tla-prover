---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(*--------------------------------------------------------------------
  BoundedSeq: a finite version of Seq over the three concrete values.
---------------------------------------------------------------------*)
BoundedSeq ==
  UNION { [1..n -> {A, B, C}] : n \in 0..bound }

(*--------------------------------------------------------------------
  Helper definitions
---------------------------------------------------------------------*)
Values == {A, B, C}

Count(seq, el) ==
  Cardinality({ j \in DOMAIN seq : seq[j] = el })

CountPrefix(seq, i, el) ==
  (* number of occurrences of el in the prefix seq[1 .. i-1] *)
  Cardinality({ j \in 1..(i-1) : j \in DOMAIN seq /\ seq[j] = el })

(*--------------------------------------------------------------------
  Variables
---------------------------------------------------------------------*)
VARIABLES seq, i, cand, cnt

(*--------------------------------------------------------------------
  Type correctness invariant
---------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in BoundedSeq
  /\ i \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

(*--------------------------------------------------------------------
  Initial state
---------------------------------------------------------------------*)
Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

(*--------------------------------------------------------------------
  Transition relation (the Boyer‑Moore scan)
---------------------------------------------------------------------*)
Next ==
  \/ /\ i <= Len(seq)
     /\ cnt = 0
     /\ cand' = seq[i]
     /\ cnt' = 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i <= Len(seq)
     /\ cnt > 0
     /\ seq[i] = cand
     /\ cand' = cand
     /\ cnt' = cnt + 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i <= Len(seq)
     /\ cnt > 0
     /\ seq[i] # cand
     /\ cand' = cand
     /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i > Len(seq)
     /\ UNCHANGED <<seq, i, cand, cnt>>

Spec ==
  Init /\ [][Next]_<<seq, i, cand, cnt>>

(*--------------------------------------------------------------------
  Correctness property: if a true majority exists it must be the
  final candidate after the scan has finished.
---------------------------------------------------------------------*)
Majority(el) ==
  Count(seq, el) > Len(seq) / 2

Correct ==
  /\ i = Len(seq) + 1        \* scan finished
  /\ \A el \in Values :
        (Majority(el) => cand = el)

(*--------------------------------------------------------------------
  Inductive invariant
---------------------------------------------------------------------*)
Inv ==
  cnt = 2 * CountPrefix(seq, i, cand) - (i - 1)

====