---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

(*----------------------------------------------------------------------
  Constants
----------------------------------------------------------------------*)
CONSTANT A, B, C, bound, Seq

(*----------------------------------------------------------------------
  The set of possible element values
----------------------------------------------------------------------*)
Values == {A, B, C}

(*----------------------------------------------------------------------
  Bounded sequences: all functions from 1..n to Values for n \in 0..bound
----------------------------------------------------------------------*)
BoundedSeq == UNION { { [i \in 1..n |-> v] : v \in Values } : n \in 0..bound }

(*----------------------------------------------------------------------
  Variables inherited from the main majority vote specification
----------------------------------------------------------------------*)
VARIABLES seq, i, cand, cnt

(*----------------------------------------------------------------------
  Initial state
----------------------------------------------------------------------*)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(*----------------------------------------------------------------------
  Scan action (the three‑case logic of the Boyer‑Moore algorithm)
----------------------------------------------------------------------*)
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
       IF cnt = 0 THEN
          /\ cand' = x
          /\ cnt'  = 1
       ELSE IF cand = x THEN
          /\ cnt' = cnt + 1
          /\ UNCHANGED cand
       ELSE
          /\ cnt' = cnt - 1
          /\ UNCHANGED cand
    /\ i' = i + 1
    /\ UNCHANGED seq

(*----------------------------------------------------------------------
  Skip action to allow stuttering when the scan is finished
----------------------------------------------------------------------*)
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED << seq, i, cand, cnt >>

(*----------------------------------------------------------------------
  Next-state relation
----------------------------------------------------------------------*)
Next == Scan \/ Done

(*----------------------------------------------------------------------
  Specification
----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(*----------------------------------------------------------------------
  Type correctness invariant
----------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(*----------------------------------------------------------------------
  Main correctness invariant (the one described in the natural text)
  After a complete scan, if there is a true majority element in seq,
  it must be equal to cand.
----------------------------------------------------------------------*)
Correct ==
    ( i > Len(seq) ) =>
        ( \A x \in Values :
            ( Cardinality({ j \in 1..Len(seq) : seq[j] = x }) > Len(seq) / 2 )
                => cand = x )

(*----------------------------------------------------------------------
  Inductive invariant (captures the classic Boyer‑Moore invariant)
----------------------------------------------------------------------*)
Inv ==
    /\ cnt >= 0
    /\ ( cnt = 0 => cand \in Values )
    /\ ( i > Len(seq) => cnt = 0 \/ cnt = 1 )
    /\ ( i <= Len(seq) => 
            cnt = Cardinality({ j \in 1..(i-1) : seq[j] = cand }) -
                   Cardinality({ j \in 1..(i-1) : seq[j] # cand }) )

=============================================================================