---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS A, B, C, bound

ASSUME /\ A /= B /\ B /= C /\ A /= C
ASSUME bound \in Nat

(*-----------------------------------------------------------------
  Bounded sequence operator (replaces Seq from Sequences)
-----------------------------------------------------------------*)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES seq, pos, cand, cnt

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Values == {A, B, C}
Vars   == <<seq, pos, cand, cnt>>

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

(*-----------------------------------------------------------------
  Scan action (the Boyer‑Moore step)
-----------------------------------------------------------------*)
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
         IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
         ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
         ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

(*-----------------------------------------------------------------
  Stuttering action after the scan is complete
-----------------------------------------------------------------*)
Done ==
    /\ pos > Len(seq)
    /\ UNCHANGED Vars

Next == Scan \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_Vars /\ WF_Vars(Scan)

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

Inv ==
    cnt >= 0

Correct ==
    /\ pos > Len(seq)
    => \A v \in Values :
          (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2) => v = cand

(*-----------------------------------------------------------------
  Exported identifiers required by the .cfg file
-----------------------------------------------------------------*)
SPECIFICATION Spec
INVARIANTS TypeOK, Correct, Inv

====