---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Constants                                                             *)
(***************************************************************************)
CONSTANT Value

(***************************************************************************)
(*  Types                                                                 *)
(***************************************************************************)
TypeOK == 
   /\ value \in Value
   /\ seq \in Seq(Value)
   /\ maxIdx \in Nat
   /\ maxIdx = Len(seq)

(***************************************************************************)
(*  Variables                                                             *)
(***************************************************************************)
VARIABLES value, seq, maxIdx, i, candidate, count

(***************************************************************************)
(*  Helper definitions                                                   *)
(***************************************************************************)
\* Number of occurrences of element v in the prefix seq[1..i]
Occurances(v, i) == Cardinality({j \in 1..i : seq[j] = v})

(***************************************************************************)
(*  Init                                                                  *)
(***************************************************************************)
Init ==
   /\ value \in Value
   /\ seq \in Seq(Value)
   /\ maxIdx = Len(seq)
   /\ i = 0
   /\ candidate = value           \* arbitrary initial candidate
   /\ count = 0

(***************************************************************************)
(*  Next action                                                          *)
(***************************************************************************)
Next ==
   /\ i < maxIdx
   /\ i' = i + 1
   /\ IF count = 0
        THEN /\ candidate' = seq[i']
             /\ count' = 1
        ELSE IF candidate = seq[i']
                THEN /\ candidate' = candidate
                     /\ count' = count + 1
                ELSE /\ candidate' = candidate
                     /\ count' = count - 1
   /\ UNCHANGED <<value, seq, maxIdx>>

(***************************************************************************)
(*  Specification                                                        *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<i, candidate, count>>

(***************************************************************************)
(*  Invariant: type correctness                                          *)
(***************************************************************************)
Inv == 
   /\ i \in Nat
   /\ i <= maxIdx
   /\ candidate \in Value
   /\ count \in Nat
   /\ (count = 0 => candidate = value)    \* when count is zero we allow any init

(***************************************************************************)
(*  Invariant: algorithm correctness                                     *)
(***************************************************************************)
Correct == 
   /\ i = maxIdx
   /\ \A v \in Value :
        (Occurances(v, maxIdx) > maxIdx / 2) => v = candidate

(***************************************************************************)
(*  THEOREM (optional, for readability)                                  *)
(***************************************************************************)
THEOREM SpecImpliesInv == Spec => []Inv

=============================================================================