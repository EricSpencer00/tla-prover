---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS A, B, C, bound

(*-------------------------------------------------------------------*)
(* Helper definitions *)

Len(s) == IF s = {} THEN 0 ELSE Max(DOMAIN s)

BoundedSeq == { s \in [Nat -> {A, B, C}] :
                  /\ Len(s) \in 0..bound
                  /\ ( Len(s) = 0 => s = {} )
                  /\ ( Len(s) > 0 => DOMAIN s = 1..Len(s) ) }

Values == {A, B, C}

(*-------------------------------------------------------------------*)
(* Variables *)

VARIABLES seq, i, cand, cnt

(*-------------------------------------------------------------------*)
(* Initialization *)

Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(*-------------------------------------------------------------------*)
(* Next-state relation *)

NextAction ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
       IF cnt = 0 THEN
          /\ cand' = x
          /\ cnt'  = 1
       ELSE IF x = cand THEN
          /\ cand' = cand
          /\ cnt'  = cnt + 1
       ELSE
          /\ cand' = cand
          /\ cnt'  = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

Next ==
    \/ NextAction
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(*-------------------------------------------------------------------*)
(* Specification *)

Spec ==
    Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_<<seq, i, cand, cnt>>(NextAction)

(*-------------------------------------------------------------------*)
(* Invariants *)

TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

Majority(e) ==
    /\ e \in Values
    /\ Cardinality({ j \in DOMAIN seq : seq[j] = e }) > Len(seq) / 2

Correct ==
    /\ i > Len(seq) => \A e \in Values : Majority(e) => e = cand

Inv == TypeOK

(*-------------------------------------------------------------------*)
(* Exported identifiers *)

SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Correct
INVARIANT Inv

====