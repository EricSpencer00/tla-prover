---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (must be declared in the .cfg)
\* ----------------------------------------------------------------------
CONSTANT A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Derived constant: the set of possible element values
\* ----------------------------------------------------------------------
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* Bounded sequence operator.
\* For each n ∈ 0..bound, we consider all functions f whose domain is 1..n
\* and whose range is a subset of Values. The constant Seq is assumed to be
\* the set of all such functions.
\* ----------------------------------------------------------------------
Seq == { f \in [1..n -> Values] : n \in 0..bound }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* TypeOK invariant (required)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in Seq
    /\ pos \in Nat
    /\ cnt \in Nat
    /\ cand \in Values

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SeqLen == IF seq = {} THEN 0 ELSE DOMAIN seq

\* ----------------------------------------------------------------------
\* Initialization (inherits the meaning from the description)
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in Seq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Transition relation (Next) – the Boyer-Moore scan step
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pos > SeqLen
       /\ UNCHANGED <<seq, pos, cand, cnt>>
    \/ /\ pos <= SeqLen
       /\ LET x == seq[pos] IN
          \/ /\ cnt = 0
             /\ /\ cand' = x
                /\ cnt' = 1
                /\ pos' = pos + 1
          \/ /\ cnt > 0 /\ cand = x
             /\ /\ cand' = cand
                /\ cnt' = cnt + 1
                /\ pos' = pos + 1
          \/ /\ cnt > 0 /\ cand # x
             /\ /\ cand' = cand
                /\ cnt' = cnt - 1
                /\ pos' = pos + 1
          \/ /\ cand # x /\ cnt = 0
             /\ /\ cand' = cand
                /\ cnt' = 0
                /\ pos' = pos + 1

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Correctness invariant (required)
\* If a value appears more than half the times in the entire sequence,
\* then after the scan finishes (pos > SeqLen) that value must be the
\* candidate.
\* ----------------------------------------------------------------------
Correct ==
    /\ pos > SeqLen
    /\ \E v \in Values :
          ( Cardinality({ i \in 1..SeqLen : seq[i] = v }) > SeqLen / 2 )
    => cand = v

\* ----------------------------------------------------------------------
\* Inductive invariant (required)
\* The Boyer-Moore invariant relating candidate, counter, and the
\* remaining suffix of the sequence.
\* ----------------------------------------------------------------------
Inv ==
    /\ cand \in Values
    /\ cnt \in Nat
    /\ (cnt = 0 => TRUE)
    /\ (cnt > 0 => 
          \A w \in Values :
            ( ( Cardinality({ i \in pos..SeqLen : seq[i] = cand }) -
                Cardinality({ i \in pos..SeqLen : seq[i] = w }) ) = cnt )
            => w = cand ))

\* ----------------------------------------------------------------------
\* Liveness property (optional, not required by the .cfg but defined for
\* completeness)
\* ----------------------------------------------------------------------
Termination == <> (pos > SeqLen)

\* ----------------------------------------------------------------------
\* The THEOREM stanza is optional; it does not affect the required
\* identifiers but documents the specification.
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

=============================================================================