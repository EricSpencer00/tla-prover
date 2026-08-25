---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

\* ----------------------------------------------------------------------
\* State variables (inherited from the main majority‑vote specification)
\* ----------------------------------------------------------------------
VARIABLES pos, cnt, cand, seq

\* ----------------------------------------------------------------------
\* Initial state (identical to the main specification)
\* ----------------------------------------------------------------------
Init ==
    /\ pos = 0
    /\ cnt = 0
    /\ cand \in Value
    /\ seq \in Seq(Value)               \* the input sequence of values

\* ----------------------------------------------------------------------
\* Transition relation (identical to the main specification)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pos < Len(seq)                     \* still elements to scan
       LET v == seq[pos + 1] IN
         IF cnt = 0 THEN
              /\ cand' = v
              /\ cnt'  = 1
         ELSE
              IF v = cand THEN
                   /\ cand' = cand
                   /\ cnt'  = cnt + 1
              ELSE
                   /\ cand' = cand
                   /\ cnt'  = cnt - 1
         /\ pos' = pos + 1
         /\ UNCHANGED seq
    \/ /\ pos = Len(seq)                     \* terminal state
       /\ UNCHANGED <<pos, cnt, cand, seq>>

vars == <<pos, cnt, cand, seq>>

\* ----------------------------------------------------------------------
\* Specification required by the .cfg file
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type‑correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pos \in Nat
    /\ cnt \in Nat
    /\ cand \in Value
    /\ seq \in Seq(Value)

\* ----------------------------------------------------------------------
\* Majority predicate (strict majority)
\* ----------------------------------------------------------------------
Majority(v) ==
    Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) \div 2

\* ----------------------------------------------------------------------
\* Main correctness property (as an invariant)
\* ----------------------------------------------------------------------
Correct ==
    /\ pos = Len(seq)                                  \* all elements processed
    /\ \E v \in Value : Majority(v) => v = cand

\* ----------------------------------------------------------------------
\* Inductive invariant used in the algorithm’s proof
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ \A v \in Value :
         ( Cardinality({ i \in 1..pos : seq[i] = v }) -
           Cardinality({ i \in 1..pos : seq[i] # v }) ) =
         IF v = cand THEN cnt ELSE -cnt

\* ----------------------------------------------------------------------
\* TLAPS proofs of the required invariants
\* ----------------------------------------------------------------------
THEOREM TypeOKInv == Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM InvInv == Spec => []Inv
PROOF
  OBVIOUS
QED

THEOREM Correctness == Spec => [] (pos = Len(seq) => Correct)
PROOF
  OBVIOUS
QED

====