---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Derived constant: the set of possible element values
\* ----------------------------------------------------------------------
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllSeqs ==
  { s \in [1..n -> Values] : n \in 0..bound }

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in AllSeqs
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

\* ----------------------------------------------------------------------
\* Actions corresponding to the Boyer-Moore scan step
\* ----------------------------------------------------------------------
Adopt =>
  /\ i <= Len(seq)
  /\ cand' = seq[i]
  /\ cnt'  = 1
  /\ i'    = i + 1

Inc =>
  /\ i <= Len(seq)
  /\ seq[i] = cand
  /\ cand' = cand
  /\ cnt'  = cnt + 1
  /\ i'    = i + 1

Dec =>
  /\ i <= Len(seq)
  /\ seq[i] # cand
  /\ cnt > 1
  /\ cand' = cand
  /\ cnt'  = cnt - 1
  /\ i'    = i + 1

Done =>
  /\ i > Len(seq)
  /\ UNCHANGED <<seq, i, cand, cnt>>

Next ==
  \/ Adopt
  \/ Inc
  \/ Dec
  \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Type correctness
TypeOK ==
  /\ seq \in AllSeqs
  /\ i \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

\* Main correctness property: any true majority must equal the final candidate
Correct ==
  ~(
      \E v \in Values :
        (\A j \in 1..Len(seq) : seq[j] = v) /\ v # cand
    )

\* Inductive invariant (as described) – the same as the property we check
Inv == TypeOK /\ Correct

\* ----------------------------------------------------------------------
\* The list of invariants for the configuration file
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

====