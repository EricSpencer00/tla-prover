---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

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
\* The set of all finite sequences (functions from 1..n) over Values
\* with length up to the bound.
SeqSet == { s \in [1..n -> Values] : n \in 0..bound }

\* The domain of a sequence (empty set for n = 0)
SeqDomain(s) == IF DOMAIN s = {} THEN {} ELSE DOMAIN s

\* The length of a sequence (0 if empty)
SeqLen(s) == IF DOMAIN s = {} THEN 0 ELSE Card(DOMAIN s)

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in SeqSet
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ i <= SeqLen(seq)
       /\ LET cur == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = cur
              /\ cnt' = 1
          ELSE IF cand = cur THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i > SeqLen(seq)   \* scan completed, stutter
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in SeqSet
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Correctness property (majority vote)
\* If an element appears more than half the time in the sequence, then after
\* the scan completes the candidate equals that element.
\* ----------------------------------------------------------------------
Correct ==
    /\ i > SeqLen(seq)           \* scan finished
    /\ \E v \in Values :
         (Card({j \in DOMAIN seq : seq[j] = v}) > SeqLen(seq) / 2)
         => cand = v

\* ----------------------------------------------------------------------
\* Inductive invariant (not used directly by the configuration but required)
\* ----------------------------------------------------------------------
Inv ==
    /\ i \in 1..(SeqLen(seq) + 1)
    /\ (cnt = 0 => cand \in Values)   \* cand remains a valid value
    /\ (cnt > 0 => cand = 
          IF SeqLen(seq) = 0 THEN cand
          ELSE 
            \E k \in 1..(i-1) :
               \A j \in 1..k : seq[j] = cand)

\* ----------------------------------------------------------------------
\* The module must expose the identifiers required by the .cfg
\* ----------------------------------------------------------------------
\* (They are already defined with the exact names above)

====