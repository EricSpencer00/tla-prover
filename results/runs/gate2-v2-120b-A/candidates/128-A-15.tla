---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Values,   \* The set of integer values that may appear in the sequence
    MaxSeqLen, \* Upper bound on the length of the sequence (used by the .cfg)
    Seq        \* The initial sequence, nondeterministically chosen by the .cfg

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Domain == 1 .. MaxSeqLen

\* An interval is represented as a record with fields l (left) and r (right)
Interval == [l : Nat, r : Nat]

\* The set of all possible intervals that lie within the domain
AllIntervals == { [l |-> i, r |-> j] : i, j \in Domain, i <= j }

\* The pivot index must lie inside the chosen interval
Pivot(i) == { p \in Domain : i.l <= p /\ p <= i.r }

\* The lower and upper subintervals produced by partitioning around a pivot
Lower(i, p) == [l |-> i.l, r |-> p]
Upper(i, p) == [l |-> p + 1, r |-> i.r]

\* =============================================================================
\* State variables
\* =============================================================================
VARIABLES
    s,          \* The current sequence (function from Domain to Values)
    orig,       \* A copy of the original sequence, never changed
    workSet,    \* Set of intervals yet to be processed
    pc          \* Program counter: "Running" or "Done"

\* ----------------------------------------------------------------------
\* Types and domain constraints (used for TypeOK invariant)
\* ----------------------------------------------------------------------
SeqType == [i \in Domain |-> Values]

\* ----------------------------------------------------------------------
\* Permutation definition: a bijection on the domain that reorders elements
\* ----------------------------------------------------------------------
Permutation == { f \in [Domain -> Domain] :
                    \A i \in Domain : \A j \in Domain : f[i] = f[j] => i = j }

\* A sequence t is a permutation of sequence u iff there exists a bijection f
\* such that for every index i, t[i] = u[f[i]]
IsPerm(t, u) == \E f \in Permutation : \A i \in Domain : t[i] = u[f[i]]

\* ----------------------------------------------------------------------
\* Partition relation
\* ----------------------------------------------------------------------
\* Partition(s0, i, p, s1) holds iff:
\*   - Elements outside interval i are unchanged
\*   - Elements inside interval i are reordered so that every element in the
\*     lower part (indices <= p) is <= every element in the upper part (> p)
Partition(s0, i, p, s1) ==
    /\ \A j \in DOMAIN s0 :
          (j < i.l \/ j > i.r) => s1[j] = s0[j]
    /\ \A j1 \in i.l .. p :
          \A j2 \in p+1 .. i.r :
              s1[j1] <= s1[j2]
    /\ IsPerm(s1, s0)

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ s = Seq
    /\ orig = Seq
    /\ workSet = { [l |-> 1, r |-> MaxSeqLen] }
    /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Main loop action
\* ----------------------------------------------------------------------
Process ==
    /\ pc = "Running"
    /\ workSet # {}
    /\ \E i \in workSet :
          IF i.l = i.r THEN
              /\ s' = s
              /\ workSet' = workSet \ {i}
          ELSE
              /\ \E p \in Pivot(i) :
                    /\ \E s1 \in DOMAIN s :
                          Partition(s, i, p, s1)
              /\ s' = s1
              /\ workSet' = (workSet \ {i}) \cup
                           { Lower(i, p), Upper(i, p) }
    /\ pc' = "Running"

\* ----------------------------------------------------------------------
\* Termination action (stuttering)
\* ----------------------------------------------------------------------
Done ==
    /\ pc = "Running"
    /\ workSet = {}
    /\ s' = s
    /\ orig' = orig
    /\ workSet' = workSet
    /\ pc' = "Done"

\* A stuttering step after termination to avoid deadlock
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED << s, orig, workSet, pc >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Process \/ Done \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, orig, workSet, pc>>

\* ----------------------------------------------------------------------
\* TypeOK invariant (optional but required by the .cfg)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ s \in SeqType
    /\ orig \in SeqType
    /\ workSet \subseteq AllIntervals
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Full inductive invariant used by the model checker
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ \A i \in DOMAIN s : s[i] \in Values
    /\ IsPerm(s, orig)
    /\ \A i \in workSet :
          \A j \in i.l .. i.r :
               \A k \in i.l .. i.r : j < k => s[j] <= s[k]

\* ----------------------------------------------------------------------
\* Partial correctness property (the safety condition)
\* ----------------------------------------------------------------------
PCorrect ==
    pc = "Done" => /\ IsPerm(s, orig)
                     /\ \A i, j \in DOMAIN s : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Termination liveness property (referenced as a PROPERTY)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====