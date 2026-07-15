---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Inherit the main majority vote specification. For illustration we
   define the necessary parts here, but they are logically the same as
   in the original module. *)
VARIABLES seq, cand, cnt, i

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)
TypeOK ==
    /\ seq \in Seq(Value)
    /\ cand \in Value \/ {}
    /\ cnt \in Nat
    /\ i \in Nat
    /\ i <= Len(seq)

(* -------------------------------------------------------------------------
   Initial state (same as the original specification)
   ------------------------------------------------------------------------- *)
Init ==
    /\ seq = {}
    /\ cand = {}
    /\ cnt = 0
    /\ i = 0

(* -------------------------------------------------------------------------
   Transition step (same as the original specification)
   ------------------------------------------------------------------------- *)
Next ==
    \/ /\ i < Len(seq)
       /\ LET x == seq[i + 1] IN
          IF cnt = 0 THEN
              /\ cand' = {x}
              /\ cnt'  = 1
          ELSE IF x = CHOOSE y \in cand : TRUE THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED << seq >>

    \/ /\ i = Len(seq)
       /\ UNCHANGED << seq, cand, cnt, i >>

(* -------------------------------------------------------------------------
   Full specification
   ------------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<seq, cand, cnt, i>>

(* -------------------------------------------------------------------------
   Auxiliary definitions used in the correctness proof
   ------------------------------------------------------------------------- *)
Occurrences(v, s) == { j \in 1..Len(s) : s[j] = v }

StrictMajority(v) ==
    Cardinality(Occurrences(v, seq)) > Len(seq) / 2

CandidateIsOnlyMajority ==
    \A v \in Value : StrictMajority(v) => v = CHOOSE y \in cand : TRUE

(* -------------------------------------------------------------------------
   Invariants required by the .cfg
   ------------------------------------------------------------------------- *)
Inv == CandidateIsOnlyMajority

Correct == Inv

====