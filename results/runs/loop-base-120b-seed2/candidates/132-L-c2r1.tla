---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
Values == { A, B, C }

\* Bounded version of Seq: all sequences over S of length at most **bound**
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

\* Tuple of all variables for the stuttering operator
vars == << seq, pos, cand, cnt >>

\*=========================
\* Initialization
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\*=========================
\* The main step of the Boyer‑Moore scan
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
          /\ IF cnt = 0 THEN
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
    \/ /\ pos > Len(seq)
       /\ UNCHANGED << seq, pos, cand, cnt >>

\*=========================
\* Specification
Spec ==
    Init /\ [][Next]_vars

\*=========================
\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* Helper: set of values that appear as a strict majority in **seq**
MajoritySet(s) ==
    { v \in Values :
        Cardinality({ i \in 1..Len(s) : s[i] = v }) > Len(s) \div 2 }

\* Correctness property: after the scan finishes, any majority element must be the candidate
Correct ==
    /\ pos > Len(seq)     \* scan complete
    /\ \A v \in MajoritySet(seq) : cand = v

\* Simple inductive invariant (can be strengthened as needed)
Inv ==
    cnt \in Nat

====