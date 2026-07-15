---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

VARIABLES seq, idx, cand, cnt, seen

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

IdxSet == 1 .. Len(seq)

Occur(v) == { i \in IdxSet : seq[i] = v }

Maj(v) == Cardinality(Occur(v)) > Len(seq) / 2

(* ----------------------------------------------------------------------
   Initial predicate (no state is introduced here; we simply inherit
   everything from the original majority vote specification)
   ---------------------------------------------------------------------- *)

Init ==
    /\ seq \in Seq(Value)
    /\ idx = 0
    /\ cand \in Value
    /\ cnt = 0
    /\ seen = {}

(* ----------------------------------------------------------------------
   Transition relation (again, inherited from the original spec)
   ---------------------------------------------------------------------- *)

Next ==
    \/ /\ idx < Len(seq)
       /\ idx' = idx + 1
       /\ IF cnt = 0
          THEN /\ cand' = seq[idx']
               /\ cnt'  = 1
          ELSE IF cand = seq[idx']
               THEN /\ cand' = cand
                    /\ cnt'  = cnt + 1
               ELSE /\ cand' = cand
                    /\ cnt'  = cnt - 1
       /\ seen' = seen \cup {seq[idx']}
    \/ /\ idx = Len(seq)
       /\ UNCHANGED <<cand, cnt, seq, seen, idx>>

Spec == Init /\ [][Next]_<<seq, idx, cand, cnt, seen>>

(* ----------------------------------------------------------------------
   Safety properties
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ seq \in Seq(Value)
    /\ idx \in 0 .. Len(seq)
    /\ cand \in Value
    /\ cnt \in Nat
    /\ seen \subseteq Value

Correct ==
    \A v \in Value :
        Maj(v) => v = cand

(* The third invariant is the one inherited from the original specification.
   We restate it here explicitly. *)
Inv ==
    /\ cand \in Value
    /\ cnt \in Nat
    /\ (cand \in seen) \/ (cnt = 0)

=============================================================================