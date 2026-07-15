---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT Value

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Values == {0, 1, 2} \cup {v : v \in Value}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES count, candidate, index, seq

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Len == Len(seq)

Positions(i) == { j \in 1..i : seq[j] = candidate }

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
CountRange == 0..Len
CandidateRange == Values
SeqRange == 1..Len

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<count, candidate, index, seq>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ count = 0
    /\ candidate \in Values
    /\ index = 1
    /\ seq \in [SeqRange -> Values]

\* ----------------------------------------------------------------------
\* Transition action (inherits the algorithm logic)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ count = 0
       /\ /\ index \leq Len
          /\ candidate' = seq[index]
          /\ count' = 1
          /\ index' = index + 1
          /\ UNCHANGED seq
    \/ /\ count > 0 /\ index \leq Len
       /\ LET current == seq[index] IN
          IF current = candidate THEN
              /\ count' = count + 1
          ELSE
              /\ count' = count - 1
       /\ candidate' = candidate
       /\ index' = index + 1
       /\ UNCHANGED seq
    \/ /\ index > Len
       /\ UNCHANGED <<count, candidate, index, seq>>

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
\* 1. Type correctness invariant
TypeOK ==
    /\ count \in CountRange
    /\ candidate \in Values
    /\ index \in Nat
    /\ seq \in [SeqRange -> Values]

\* 2. Algorithm's main invariant (the one proved in the main spec)
Inv ==
    /\ count >= 0
    /\ candidate \in Values
    /\ index \in Nat

\* 3. Correctness invariant: any strict majority element equals the candidate
Correct ==
    \A v \in Values :
        ( Cardinality({ j \in 1..Len : seq[j] = v })
          > Len / 2 )
        => v = candidate

\* ----------------------------------------------------------------------
\* Specification name required by the .cfg file
\* ----------------------------------------------------------------------
Spec == Spec

=============================================================================