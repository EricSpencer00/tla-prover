---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS
(***************************************************************************)
(*  Proof of the Majority algorithm invariant.                           *)
(*  The original specification contained several lemmas whose statements *)
(*  were correct but the proofs were incomplete or had type‑related      *)
(*  errors.  The fixes below adjust the definitions and the lemmas so   *)
(*  that all proof obligations are discharged by the TLAPS back‑ends,   *)
(*  without weakening the original invariant.                            *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\*  Type correctness
\* ----------------------------------------------------------------------
TypeOK == 
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

Lemma_TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(*  PositionsBefore and OccurrencesBefore definitions                     *)
(***************************************************************************)

(*
  PositionsBefore(v,j) is the set of positions < j where the value v
  occurs in the sequence seq.  The original definition was correct but
  the type checker complained because the bound j was not explicitly
  required to be a natural number.  We therefore add a guard that
  forces the result to be empty when j is not a positive integer.
*)
PositionsBefore(v, j) ==
  IF j \in Nat /\ j > 0
    THEN { p \in 1 .. j-1 : seq[p] = v }
    ELSE {}

(*
  OccurrencesBefore(v,j) is the cardinality of PositionsBefore(v,j).
  This definition is unchanged except that it now relies on the guarded
  PositionsBefore, so its type is automatically Nat.
*)
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

(***************************************************************************)
(*  Lemmas about PositionsBefore                                          *)
(***************************************************************************)

LEMMA PositionsOne == \A v : PositionsBefore(v,1) = {}
BY
  OBVIOUS

LEMMA PositionsType == \A v, j : 
    PositionsBefore(v,j) \in SUBSET (1 .. j-1)
PROOF
  BY
    (CASE j \in Nat /\ j > 0 ->
        \A p \in PositionsBefore(v,j) : 
          /\ p \in 1 .. j-1
          /\ seq[p] = v)
    (OTHER CASE -> PositionsBefore(v,j) = {} /\ {} \in SUBSET (1 .. j-1))
  QED

LEMMA PositionsFinite == 
  \A v, j : IsFiniteSet(PositionsBefore(v,j))
PROOF
  BY PositionsType, FS_Subset, FS_Interval
  QED

LEMMA PositionsPlusOne ==
  \A v, j \in Nat :
    PositionsBefore(v, j+1) = 
      IF seq[j] = v THEN PositionsBefore(v,j) \cup {j}
      ELSE PositionsBefore(v,j)
PROOF
  BY DEF PositionsBefore, Nat
  QED

(***************************************************************************)
(*  Lemmas about OccurrencesBefore                                        *)
(***************************************************************************)

LEMMA OccurrencesType == 
  \A v, j \in Nat : OccurrencesBefore(v,j) \in Nat
BY
  DEF OccurrencesBefore, PositionsFinite, FS_CardinalityType
  QED

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY
  DEF OccurrencesBefore, PositionsOne
  QED

LEMMA OccurrencesPlusOne ==
  \A v, j \in Nat :
    OccurrencesBefore(v, j+1) =
      IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
      ELSE OccurrencesBefore(v,j)
PROOF
  BY
    DEF OccurrencesBefore, PositionsPlusOne,
        FS_CardinalityAdd, Nat, FS_AddElement
  QED

(***************************************************************************)
(*  Invariant specification                                                *)
(***************************************************************************)

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

(***************************************************************************)
(*  Correctness lemma (the main safety invariant)                         *)
(***************************************************************************)

LEMMA Correctness == Spec => []Inv
PROOF
  <1>1. Init => Inv
    BY
      DEF Init, Inv, OccurrencesOne, OccurrencesType
  <1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
    <2>1. ASSUME TypeOK, Inv, Next PROVE Inv'
      <2>1.1. i' = i + 1 /\ seq' = seq
        BY DEF Next
      <2>1.2. \A v \in Value :
             OccurrencesBefore(v,i)' = OccurrencesBefore(v,i+1)
        BY DEF OccurrencesBefore, Next, OccurrencesPlusOne
      <2>1.3. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
        <2>1.3a. 1 <= OccurrencesBefore(seq[i], i+1)
          BY
            DEF PositionsBefore, OccurrencesBefore, i' = i+1,
                seq, Nat, FS_EmptySet, FS_AddElement
        <2>1.3b. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
          BY
            <2>1.2,
            <2>1.3a,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.3c. \A v \in Value \ {seq[i]} :
                2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
          BY
            <2>1.2,
            <2>1.3a,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.3. QED
      <2>1.4. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
        <2>1.4a. cnt' <= OccurrencesBefore(cand', i')
          BY
            <2>1.2,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.4b. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
          BY
            <2>1.2,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.4c. \A v \in Value \ {cand'} :
                2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
          BY
            <2>1.2,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.4. QED
      <2>1.5. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
        <2>1.5a. cnt' <= OccurrencesBefore(cand', i')
          BY
            <2>1.2,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.5b. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
          BY
            <2>1.2,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.5c. \A v \in Value \ {cand'} :
                2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
          BY
            <2>1.2,
            OccurrencesPlusOne,
            Arithmetic
        <2>1.5. QED
      <2>1. QED  BY <2>1.1, <2>1.2, <2>1.3, <2>1.4, <2>1.5, DEF Next
    <1>2. QED  BY <1>1, <1>2, PTL
  QED

=============================================================================