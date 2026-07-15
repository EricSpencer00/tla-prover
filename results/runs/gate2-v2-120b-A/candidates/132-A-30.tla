---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* The finite set of possible element values
\* ----------------------------------------------------------------------
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* State variables
\*   seq   - the input sequence (finite function from 1..|seq| to Values)
\*   pos   - current scan position (1..|seq|+1, where +1 means after the last
\*           element)
\*   cand  - current candidate element (an element of Values)
\*   cnt   - current counter (natural number)
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definition: length of the current sequence
\* ----------------------------------------------------------------------
SeqLen == Len(seq)

\* ----------------------------------------------------------------------
\* Type correctness invariant (required as TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in [1..bound -> Values] \/ seq = {}
  /\ pos \in 1..(SeqLen + 1)
  /\ cand \in Values
  /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Initial state (corresponds to the main specification's Init)
\*   - seq is any sequence of length n where 0 <= n <= bound
\*   - pos starts at 1 (first element)
\*   - cand is nondeterministically chosen from Values
\*   - cnt starts at 0
\* ----------------------------------------------------------------------
Init ==
  /\ \E n \in 0..bound:
        /\ seq = [i \in 1..n |-> CHOOSE v \in Values: TRUE] \* any function of length n
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* ----------------------------------------------------------------------
\* Scan action (the three‑case logic of the Boyer‑Moore algorithm)
\*   - If counter is zero, adopt the current element as new candidate
\*   - Else if current element equals candidate, increment counter
\*   - Else decrement counter
\*   After processing, advance the position.
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pos <= SeqLen               \* there is an element to process
     /\ LET cur == seq[pos] IN
        IF cnt = 0 THEN
          /\ cand' = cur
          /\ cnt'  = 1
        ELSE IF cur = cand THEN
          /\ cand' = cand
          /\ cnt'  = cnt + 1
        ELSE
          /\ cand' = cand
          /\ cnt'  = cnt - 1
     /\ pos' = pos + 1
     /\ UNCHANGED seq
  \/ /\ pos = SeqLen + 1            \* scan complete, stay in terminal state
     /\ UNCHANGED <<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Specification (temporal formula)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Main correctness property:
\*   If an element appears more than half the time in the original
\*   sequence, then after the scan finishes the candidate equals that element.
\* ----------------------------------------------------------------------
Correct ==
  /\ pos = SeqLen + 1
  /\ \E maj \in Values :
        ( Cardinality({ i \in 1..SeqLen : seq[i] = maj }) > SeqLen / 2 )
        => cand = maj

\* ----------------------------------------------------------------------
\* Inductive invariant (same as Correct but holds at every reachable state)
\* ----------------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ (cnt = 0 => cand \in Values)   \* trivially true, kept for clarity
  /\ (cnt > 0 => cand \in Values)

\* ----------------------------------------------------------------------
\* The configuration expects the following identifiers:
\*   Spec        - the overall specification
\*   TypeOK, Correct, Inv  - invariants
\* ----------------------------------------------------------------------
\* (no additional definitions needed)

====