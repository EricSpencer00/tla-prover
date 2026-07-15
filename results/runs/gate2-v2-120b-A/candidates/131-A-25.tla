---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT Value

(*--------------------------------------------------------------------
  Variables (inherited from the main specification)
--------------------------------------------------------------------*)
VARIABLES seq, pos, cand, count, maj, result

(*--------------------------------------------------------------------
  Types (used for the TypeOK invariant)
--------------------------------------------------------------------*)
ValueSet == {v \in Value : TRUE}
SeqPos   == 1 .. Len(seq)

(*--------------------------------------------------------------------
  Derived definitions
--------------------------------------------------------------------*)
Occurrences(v) == { i \in 1..Len(seq) : seq[i] = v }

(*--------------------------------------------------------------------
  Initial state (inherited from the main specification)
--------------------------------------------------------------------*)
Init ==
    /\ seq \in Seq(Value)            \* the input sequence of values
    /\ pos = 1
    /\ cand \in Value
    /\ count = 0
    /\ maj = {}
    /\ result = {}

(*--------------------------------------------------------------------
  Next-state relation (inherited from the main specification)
--------------------------------------------------------------------*)
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET v == seq[pos] IN
          /\ IF count = 0 THEN
                /\ cand' = v
                /\ count' = 1
             ELSE IF cand = v THEN
                /\ count' = count + 1
             ELSE
                /\ count' = count - 1
          /\ pos' = pos + 1
          /\ UNCHANGED <<seq, cand, maj, result>>
    \/ /\ pos > Len(seq)               \* after scanning
       /\ maj' = { v \in Value : Cardinality(Occurrences(v)) > Len(seq) / 2 }
       /\ result' = cand
       /\ UNCHANGED <<seq, pos, cand, count>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, pos, cand, count, maj, result>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in Seq(Value)
    /\ pos \in Nat
    /\ cand \in Value
    /\ count \in Nat
    /\ maj \subseteq Value
    /\ result \in Value

Inv ==
    /\ (pos > Len(seq) => result = cand)
    /\ (pos > Len(seq) => maj = { v \in Value : Cardinality(Occurrences(v)) > Len(seq) / 2 })

Correct ==
    (\A v \in Value :
        (Cardinality(Occurrences(v)) > Len(seq) / 2) => v = result)

(*--------------------------------------------------------------------
  THEOREM (optional, for TLAPS)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

====