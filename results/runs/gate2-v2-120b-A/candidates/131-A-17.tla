---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Constants                                                             *)
(***************************************************************************)
CONSTANT Value

(***************************************************************************)
(*  Derived sets                                                          *)
(***************************************************************************)
Values == {v \in Value : TRUE}

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES seq, i, cand, cnt

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)
(* seq is the input sequence of values; it is assumed to be a sequence of *)
(* elements drawn from the set Values. No new state variable introduces     *)
(* seq, but we declare it here to make the module self‑contained.            *)
SeqOK == seq \in Seq(Values)

(* The finite set of positions before the current index i (exclusive). *)
PositionsBefore == {j \in 1..Len(seq) : j < i}

(***************************************************************************)
(*  Initial state (inherits the initialization of the original algorithm) *)
(***************************************************************************)
Init ==
    /\ seq \in Seq(Values)          \* arbitrary finite sequence of values
    /\ i = 1
    /\ cand = CHOOSE v \in Values : TRUE  \* any value, will be updated
    /\ cnt = 0
    /\ cand \in Values
    /\ cnt \in Nat

(***************************************************************************)
(*  Next-state relation (inherits the original algorithm actions)          *)
(***************************************************************************)
Next ==
    \/ /\ i <= Len(seq)
       /\ IF i > Len(seq) THEN FALSE
          ELSE
            IF cnt = 0 THEN
               /\ cand' = seq[i]
               /\ cnt'  = 1
            ELSE
               /\ IF seq[i] = cand THEN cnt' = cnt + 1
                  ELSE cnt' = cnt - 1
               /\ cand' = cand
       /\ i' = i + 1
    \/ /\ i > Len(seq)            \* stutter after the scan is finished
       /\ UNCHANGED <<cand, cnt, i, seq>>

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<cand, cnt, i, seq>>

(***************************************************************************)
(*  Type correctness invariant                                            *)
(***************************************************************************)
TypeOK ==
    /\ seq \in Seq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat
    /\ i <= Len(seq) + 1               \* i may be one past the last index

(***************************************************************************)
(*  Main correctness invariant                                            *)
(***************************************************************************)
(* After the scan (i = Len(seq) + 1), any value that appears in a strict   *)
(* majority of the positions must be equal to cand.                         *)
Inv ==
    \/ i <= Len(seq)          \* before the scan is complete, Inv holds trivially
    \/ /\ i = Len(seq) + 1
       /\ \A v \in Values :
            ( Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq) / 2 )
            => v = cand

(***************************************************************************)
(*  The property requested by the .cfg file                                *)
(***************************************************************************)
Correct == Inv

(***************************************************************************)
(*  Theorem (optional, for TLAPS)                                         *)
(***************************************************************************)
THEOREM Spec => []Inv

====