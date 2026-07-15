---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* Constants *)
CONSTANT Value

(***************************************************************************)
(* Types *)
Element == Value
Seq == Seq(Element)

(***************************************************************************)
(* Variables *)
VARIABLES seq, i, candidate, count

(***************************************************************************)
(* Helper definitions *)
Positions(i) == 1 .. i
PositionsBefore(i) == IF i = 1 THEN {} ELSE 1 .. (i - 1)

\* Count occurrences of element e in positions 1..i of the sequence.
Occur(seq, i, e) == 
  Cardinality({ j \in Positions(i) : seq[j] = e })

\* The set of elements that appear in a strict majority in the entire sequence.
MajSeq(seq) == { e \in Value : 2 * Occur(seq, Len(seq), e) > Len(seq) }

\* The set of elements that appear in a strict majority among the first i positions.
MajPrefix(seq, i) == { e \in Value : 2 * Occur(seq, i, e) > i }

\* Type correctness predicate.
TypeOK == 
  /\ seq \in Seq
  /\ i \in Nat
  /\ candidate \in Value \cup {None}
  /\ count \in Nat

(***************************************************************************)
(* Initialization *)
Init == 
  /\ seq = << >>
  /\ i = 0
  /\ candidate = None
  /\ count = 0
  /\ TypeOK

(***************************************************************************)
(* Next-state relation *)
Next == 
  \/ /\ i < Len(seq)
     /\ LET nxt == i + 1 IN
        /\ IF count = 0 THEN
              /\ candidate' = seq[nxt]
              /\ count' = 1
           ELSE 
              /\ IF candidate = seq[nxt] THEN
                    /\ count' = count + 1
                 ELSE
                    /\ count' = count - 1
              /\ candidate' = candidate
        /\ i' = nxt
        /\ UNCHANGED seq
  \/ /\ i = Len(seq)          \* stay after the scan finishes
        /\ UNCHANGED <<i, candidate, count, seq>>
  \/ /\ i = 0                 \* start processing a new input sequence
        /\ \E newSeq \in Seq :
              /\ seq' = newSeq
              /\ i' = 0
              /\ candidate' = None
              /\ count' = 0
              /\ UNCHANGED <<>>

(***************************************************************************)
(* Specification *)
Spec == Init /\ [][Next]_<<seq, i, candidate, count>>

(***************************************************************************)
(* Main correctness invariant *)
Correct == 
  /\ i = Len(seq)
  /\ \A e \in MajSeq(seq) : e = candidate

(***************************************************************************)
(* The inductive invariant from the main specification (mirrored here) *)
Inv == 
  /\ candidate \in Value \cup {None}
  /\ count \in Nat
  /\ i \in Nat
  /\ i <= Len(seq)
  /\ \A e \in Value :
        ((candidate = e) => (Occur(seq, i, e) >= count)) 
        /\ ((candidate # e) => (Occur(seq, i, e) < count))

(***************************************************************************)
(* THEOREMS / PROOFS *)
THEOREM InitTypeOK == Init => TypeOK

THEOREM NextPreservesInv == 
  Inv /\ [Next]_<<seq, i, candidate, count>> => Inv'

THEOREM InvImpliesCorrect == 
  Inv => Correct

THEOREM SpecImpliesInv == Spec => []Inv

THEOREM SpecImpliesCorrect == Spec => []Correct

=============================================================================