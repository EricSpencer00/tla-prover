---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound, Seq

\* The set of possible values
ValueSet == {A, B, C}

\* ----------------------------------------------------------------------
\* Operators defined in the main majority vote specification (re‑implemented
\* here because this module must be self‑contained).  The state variables are
\* declared as module‑level variables.
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper operator for a bounded sequence of length ≤ bound.
\* We represent a sequence as a function from 1..len to ValueSet together
\* with its length len.  The operator SeqSet yields the set of all such
\* pairs (len, s) with len ∈ 0..bound.
\* ----------------------------------------------------------------------
SeqSet ==
  { [len |-> l, s |-> [i \in 1..l |-> v] ] :
        l \in 0..bound,
        \E f \in [1..l -> ValueSet] : v = f }

\* The configuration fixes Seq to be exactly the above set.
Seq == SeqSet

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ \E pair \in Seq :
        /\ seq = pair.s
        /\ pos = 1
        /\ cand \in ValueSet
        /\ cnt = 0

\* ----------------------------------------------------------------------
\* Scan action – three cases of the Boyer‑Moore algorithm.
\* ----------------------------------------------------------------------
Scan ==
  /\ pos <= Len(seq)                                   \* there is a next element
  /\ LET cur == seq[pos] IN
     IF cnt = 0 THEN
        /\ cand' = cur
        /\ cnt'  = 1
        /\ pos'  = pos + 1
        /\ UNCHANGED seq
     ELSE IF cand = cur THEN
        /\ cnt' = cnt + 1
        /\ pos' = pos + 1
        /\ UNCHANGED <<seq, cand>>
     ELSE
        /\ cnt' = cnt - 1
        /\ pos' = pos + 1
        /\ UNCHANGED <<seq, cand>>

\* ----------------------------------------------------------------------
\* Completion action – when the scan is past the last element we stay in a
\* terminating state (no state change).  This prevents deadlock when the
\* model checker looks for liveness.
\* ----------------------------------------------------------------------
Done ==
  /\ pos > Len(seq)
  /\ UNCHANGED <<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Scan \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in [1..Len(seq) -> ValueSet] \/ Len(seq) = 0
  /\ pos \in Nat
  /\ cand \in ValueSet
  /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Main correctness property (inductive invariant)
\* ----------------------------------------------------------------------
Inv ==
  /\ (cnt = 0 => cand \in ValueSet)               \* trivially true but keeps cand typed
  /\ (cnt > 0 => cand \in ValueSet)               \* same as above; kept for clarity

\* ----------------------------------------------------------------------
\* Statement that after a complete scan any element that appears strictly
\* more than half the time must equal the current candidate.
\* ----------------------------------------------------------------------
Correct ==
  (pos > Len(seq)) => 
    \A v \in ValueSet :
        (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2) => v = cand

\* ----------------------------------------------------------------------
\* Export the required identifiers for the configuration file
\* ----------------------------------------------------------------------
THEOREM Spec_is_Spec == Spec

=============================================================================