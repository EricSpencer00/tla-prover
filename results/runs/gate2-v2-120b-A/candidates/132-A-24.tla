---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----- Constants (to be bound in the .cfg) -----
CONSTANT A, B, C, bound, Seq

\* The set of possible values
Values == {A, B, C}

\* ----- State variables -----
VARIABLES seq, pos, cand, cnt

\* ----- Bounded sequence operator (all sequences of length ≤ bound) -----
BoundedSeq == 
    \E n \in 0..bound : 
        \E f \in [1..n -> Values] : 
            \A i \in 1..n : f[i] = Seq[i]

\* For convenience we also define a helper that extracts the finite function
\* representing the actual sequence up to its length.  In this model we store
\* the entire sequence as a function from 1..bound to Values, padding the
\* unused positions with an arbitrary element (say, A).  The predicate
\* BoundedSeq ensures that only the prefix up to the real length matters.
BSeq == [i \in 1..bound |-> 
            IF i <= Len(seq) THEN seq[i] ELSE A]

\* ----- Initial state -----
Init ==
    /\ seq \in Seq
    /\ Len(seq) \in 0..bound
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* ----- Helper to compute the length of seq (since seq may be a function with a
\* domain that is a subset of 1..bound) -----
Len(s) == 
    IF s = {} THEN 0 ELSE Max(Domain(s))

\* ----- Action: scan the next element -----
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ /\ pos > Len(seq)   \* scan already complete, stay idle
       /\ UNCHANGED <<seq, pos, cand, cnt>>

\* ----- Specification -----
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----- Type correctness invariant -----
TypeOK ==
    /\ seq \in Seq
    /\ Len(seq) \in 0..bound
    /\ pos \in 1..(Len(seq) + 1)
    /\ cand \in Values
    /\ cnt \in Nat

\* ----- Majority correctness invariant -----
Correct ==
    \A n \in 0..bound :
        \A s \in Seq :
            ( /\ Len(s) = n
              /\ \A x \in Values :
                    (Cardinality({ i \in 1..n : s[i] = x }) > n/2) =>
                    (cand = x) )
                \/ ~\E x \in Values :
                    Cardinality({ i \in 1..n : s[i] = x }) > n/2)

\* ----- Inductive invariant (same as Correct for this model) -----
Inv == Correct

\* ----- Liveness property: scan eventually completes -----
Complete == pos > Len(seq)

\* ----- The identifiers required by the .cfg -----
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Correct
INVARIANT Inv
PROPERTY Complete

====