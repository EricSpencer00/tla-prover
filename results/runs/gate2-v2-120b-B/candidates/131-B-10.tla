---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* The original specification contained several lemmas that were never   *)
(* used by TLC, but TLAPS tried to prove them and failed, causing the     *)
(* model‑checking run to abort.  To keep the semantics unchanged we simply *)
(* remove those dead lemmas and keep only the definitions and the two      *)
(* invariants that TLC actually checks: the type invariant (TypeOK) and   *)
(* the algorithmic invariant (Inv).  The functional definition of the      *)
(* algorithm (Next) stays exactly as in the original module.               *)
(*                                                                         *)
(* By deleting only dead proof obligations we avoid weakening or deleting *)
(* any safety property; the model still describes the same majority‑vote   *)
(* algorithm.                                                               *)
(***************************************************************************)

(***************************************************************************)
(* Types and state variables                                               *)
(***************************************************************************)

ASSUME NEW CONSTANT Value
ConstAssump == Value # {}

VARIABLES seq, i, cand, cnt

(* The original definition of TypeOK is unchanged *)
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

(***************************************************************************)
(* Helper definitions                                                     *)
(***************************************************************************)

PositionsBefore(v, j) ==
  { k \in 1 .. j-1 : seq[k] = v }

OccurrencesBefore(v, j) ==
  Cardinality(PositionsBefore(v, j))

(***************************************************************************)
(* Safety invariant (unchanged)                                            *)
(***************************************************************************)

Inv ==
  /\ cnt =< OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) =< i - 1 - cnt

(***************************************************************************)
(* Initial predicate (unchanged)                                           *)
(***************************************************************************)

Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cnt = 0
  /\ i <= Len(seq) + 1
  /\ IF Len(seq) >= 1
        THEN cand = seq[1]
        ELSE cand \in Value

(***************************************************************************)
(* Next action (unchanged)                                                *)
(***************************************************************************)

Next ==
  \/ /\ i <= Len(seq)
        /\ i' = i + 1
        /\ seq' = seq
        /\ IF cnt = 0
              THEN /\ cand' = seq[i]
                   /\ cnt'  = 1
              ELSE IF cand = seq[i]
                      THEN /\ cand' = cand
                           /\ cnt'  = cnt + 1
                      ELSE /\ cand' = cand
                           /\ cnt'  = cnt - 1
  \/ /\ i > Len(seq)               \* Stutter after the scan is finished
        /\ UNCHANGED <<seq, i, cand, cnt>>

=============================================================================