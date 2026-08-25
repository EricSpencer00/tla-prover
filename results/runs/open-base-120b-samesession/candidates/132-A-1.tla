---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(*-----------------------------------------------------------------
  Assumptions about the constants
-----------------------------------------------------------------*)
ASSUME A # B /\ A # C /\ B # C
ASSUME bound \in Nat

(*-----------------------------------------------------------------
  The set of concrete elements
-----------------------------------------------------------------*)
ElemSet == { A, B, C }

(*-----------------------------------------------------------------
  BoundedSeq: finite sequences of length at most bound
-----------------------------------------------------------------*)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ seq \in BoundedSeq(ElemSet)
    /\ i = 1
    /\ cand \in ElemSet
    /\ cnt = 0

(*-----------------------------------------------------------------
  Scanning action (the Boyer‑Moore step)
-----------------------------------------------------------------*)
Scan ==
    /\ i <= Len(seq)
    /\ i' = i + 1
    /\ UNCHANGED seq
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

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Scan]_vars /\ WF_vars(Scan)

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ seq \in BoundedSeq(ElemSet)
    /\ i \in Nat
    /\ cand \in ElemSet
    /\ cnt \in Nat

(*-----------------------------------------------------------------
  Majority predicate
-----------------------------------------------------------------*)
Majority(v) ==
    Len(seq) > 0 /\ 
    Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2

(*-----------------------------------------------------------------
  Correctness property:
  after the scan finishes, if a majority exists then the candidate
  is a majority element.
-----------------------------------------------------------------*)
Correct ==
    ( \E v \in ElemSet : Majority(v) ) => ( i > Len(seq) => Majority(cand) )

(*-----------------------------------------------------------------
  Inductive invariant (here we reuse the type invariant)
-----------------------------------------------------------------*)
Inv == TypeOK

=============================================================================