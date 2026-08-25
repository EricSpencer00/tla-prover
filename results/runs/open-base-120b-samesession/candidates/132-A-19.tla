---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* ----------------------------------------------------------------------
\* Value set of the model
\* ----------------------------------------------------------------------
ValueSet == { A, B, C }

\* ----------------------------------------------------------------------
\* BoundedSeq(S) : finite version of Seq(S) limited by the constant bound
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, candidate, counter

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SeqLen == Len(seq)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos = 1
    /\ candidate \in ValueSet
    /\ counter = 0

\* ----------------------------------------------------------------------
\* One step of the Boyer‑Moore scan
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pos <= SeqLen
       /\ LET e == seq[pos] IN
          CASE
            counter = 0 -> 
                /\ candidate' = e
                /\ counter' = 1
            /\ counter # 0 /\ e = candidate ->
                /\ candidate' = candidate
                /\ counter' = counter + 1
            /\ counter # 0 /\ e # candidate ->
                /\ candidate' = candidate
                /\ counter' = counter - 1
          END CASE
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq>>
    \/ /\ pos > SeqLen
       /\ UNCHANGED <<seq, pos, candidate, counter>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, candidate, counter>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos \in Nat
    /\ candidate \in ValueSet
    /\ counter \in Nat

\* ----------------------------------------------------------------------
\* Majority‑correctness invariant
\* ----------------------------------------------------------------------
MajoritySet ==
    { v \in ValueSet :
        Cardinality({ i \in 1..SeqLen : seq[i] = v }) > SeqLen / 2 }

Correct ==
    (pos > SeqLen) => (MajoritySet = {} \/ candidate \in MajoritySet)

\* ----------------------------------------------------------------------
\* Inductive invariant (can be strengthened later)
\* ----------------------------------------------------------------------
Inv == TypeOK

====