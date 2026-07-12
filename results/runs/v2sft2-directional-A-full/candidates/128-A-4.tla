---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Domain == 1 .. MaxSeqLen

\* A sequence over Domain with values drawn from the specified constant set
SeqType == {s \in Seq[Values] : Cardinality(s) <= MaxSeqLen}

\* An interval is a two-element tuple [low, high] where low <= high and both are in Domain
Interval == {i \in [low \in Domain, high \in Domain] : i.low \leq i.high}

\* A set of intervals
Intervals == SUBSET Interval

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

Init ==
    /\ seq \in SeqType
    /\ orig = seq
    /\ work = { [low |-> 1, high |-> Cardinality(seq)] }
    /\ pc \in {"main", "halt"}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A permutation of a sequence is another sequence of the same length that
\* contains exactly the same multiset of elements.
Perm[s, t] == Cardinality(s) = Cardinality(t) /\ \A i \in 1..Cardinality(s) : (i \in s) = (i \in t)

\* Partition operator: given a sequence s, an interval [l..h], and a pivot p
\* (where l <= p <= h), it nondeterministically returns a new sequence s' such that:
\* 1. Elements outside [l..h] are unchanged.
\* 2. The multiset of elements inside [l..h] is unchanged (permutes).
\* 3. The element at index p is the pivot chosen by the partition procedure.
\* 4. All elements at or before p are <= all elements after p.
Partition(s, l, h, p) ==
    \E t \in SeqType :
        /\ Cardinality(t) = Cardinality(s)
        /\ \A i \in 1..Cardinality(s) :
              (i < l \/ i > h) => t[i] = s[i]
        /\ Perm[s[l..h], t[l..h]]
        /\ t[p] = s[p]
        /\ \A i \in l..p : t[i] \leq \E j \in p+1..h : t[j]

\* ----------------------------------------------------------------------
\* Next-state relation (one step of the algorithm)
\* ----------------------------------------------------------------------
Next ==
    /\ pc = "main"
    /\ work \neq {}
    /\ \E i \in work :
          /\ i.low < i.high
          /\ \E p \in i.low..i.high :
                /\ p \in Domain
                /\ \E i' \in work :
                       /\ i' = [low |-> i.low, high |-> p-1]
                       /\ i' \in work
                /\ \E i'' \in work :
                       /\ i'' = [low |-> p+1, high |-> i.high]
                       /\ i'' \in work
                /\ seq' = Partition(seq, i.low, i.high, p)
                /\ work' = (work \ {i}) \cup {i', i''}
                /\ pc' = pc
    \/ /\ pc = "main"
    /\ work = {}
    /\ pc' = "halt"
    \/ /\ pc = "halt"
    /\ pc' = pc

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, work, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in SeqType
    /\ work \subseteq Interval
    /\ pc \in {"main", "halt"}

\* ----------------------------------------------------------------------
\* Partial correctness invariant (sorted permutation)
\* ----------------------------------------------------------------------
Sorted(s) ==
    /\ \A i,j \in 1..Cardinality(s) : (i < j) => s[i] <= s[j]

PCorrect ==
    /\ pc = "halt"
    /\ Perm[seq, orig]
    /\ Sorted(seq)

\* ----------------------------------------------------------------------
\* Composite invariant used for TLC
\* ----------------------------------------------------------------------
Inv == TypeOK /\ (pc = "halt" => PCorrect)

\* ----------------------------------------------------------------------
\* Liveness property (weak fairness on termination)
\* ----------------------------------------------------------------------
Termination ==
    WF_Exists Next

====