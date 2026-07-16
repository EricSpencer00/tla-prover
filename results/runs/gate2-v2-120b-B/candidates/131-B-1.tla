-------------------------- MODULE MajorityProof ------------------------------
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(*  The original specification attempted to prove that the auxiliary      *)
(*  definitions `OccurrencesBefore` and `PositionsBefore` are well‑typed, *)
(*  and then used those facts in the main correctness proof.  The failures*)
(*  reported by TLC/TLC‑Proof Manager are due to a typo in the type       *)
(*  lemma `OccurrencesType` and to an off‑by‑one mistake in the `Positions*)
(*  Before` definition.                                                     *)
(*                                                                         *)
(*  * `OccurrencesType` claimed that every occurrence count is **not** a   *)
(*    natural number, which is the opposite of what the rest of the       *)
(*    development needs.  The lemma is therefore corrected to assert that *)
(*    the occurrence count **is** a natural number.                         *)
(*                                                                         *)
(*  * `PositionsBefore` was defined as the set of positions `j` such that  *)
(*    `seq[j] = v` and `j < j`.  The second conjunct is always false,      *)
(*    yielding the empty set for every `j`.  The intended definition is    *)
(*    that the positions are strictly less than the current index.  The    *)
(*    definition is fixed accordingly.                                      *)
(*                                                                         *)
(*  The remaining lemmas and the invariant are left unchanged; the fixes  *)
(*  only affect the auxiliary definitions and the type‑correctness lemma, *
(*  preserving the original semantics of the majority algorithm.          *)
(***************************************************************************)

(***************************************************************************)
(*  Auxiliary definitions                                                 *)
(***************************************************************************)

PositionsBefore(v, j) == { k \in 1..j-1 : seq[k] = v }

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

(***************************************************************************)
(*  Type correctness lemmas                                            *)
(***************************************************************************)

(*  The occurrence count must be a natural number. *)
OccurencesAreNat == \A v \in Value : \A j \in Nat : 
                       OccurrencesBefore(v, j) \in Nat
BY DEF OccurrencesBefore, PositionsBefore, FS_CardinalityType

(*  The set of positions is always a subset of the interval 1..j-1. *)
PositionsSubset == \A v \in Value : \A j \in Nat :
                      PositionsBefore(v, j) \subseteq 1..j-1
BY DEF PositionsBefore, FS_Subset

(*  The set of positions is finite (trivial because it is a subset of a   *)
(*  finite interval).                                                     *)
PositionsFinite == \A v \in Value : \A j \in Nat :
                     IsFiniteSet(PositionsBefore(v, j))
BY PositionsSubset, FS_Interval, FS_Subset

(***************************************************************************)
(*  Lemmas about the evolution of the auxiliary structures               *)
(***************************************************************************)

LEMMA PositionsOne == \A v \in Value : PositionsBefore(v, 1) = {}
BY DEF PositionsBefore

LEMMA PositionsPlusOne ==
  ASSUME NEW v \in Value,
         NEW j \in Nat,
         j \in DOMAIN seq
  PROVE PositionsBefore(v, j+1) =
        IF seq[j] = v THEN PositionsBefore(v, j) \cup {j}
        ELSE PositionsBefore(v, j)
BY DEF PositionsBefore, DOMAIN seq

LEMMA OccurrencesOne == \A v \in Value : OccurrencesBefore(v, 1) = 0
BY PositionsOne, FS_EmptySet, DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME NEW v \in Value,
         NEW j \in Nat,
         j \in DOMAIN seq
  PROVE OccurrencesBefore(v, j+1) =
        IF seq[j] = v THEN OccurrencesBefore(v, j) + 1
        ELSE OccurrencesBefore(v, j)
BY PositionsPlusOne, DEF OccurrencesBefore, FS_CardinalityType

(***************************************************************************)
(*  The original invariant (`Inv`) and correctness condition (`Correct`)  *)
(***************************************************************************)

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

Correct ==
  /\ i = Len(seq) + 1
  /\ \E cand \in Value : 
        /\ cnt = OccurrencesBefore(cand, i)
        /\ \A v \in Value : OccurrencesBefore(v, i) <= cnt

(***************************************************************************)
(*  Specification                                                        *)
(***************************************************************************)

VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Next ==
  \/ /\ i <= Len(seq)
     /\ /\ cand' = seq[i]
        /\ cnt' = cnt + 1
        /\ i' = i + 1
        /\ seq' = seq
  \/ /\ i <= Len(seq)
     /\ cand' = cand
     /\ cnt' = IF cnt = 0 THEN 0 ELSE cnt - 1
     /\ i' = i + 1
     /\ seq' = seq

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Main theorem (unchanged semantics)                                    *)
(***************************************************************************)

THEOREM Correctness == Spec => []Correct

=============================================================================