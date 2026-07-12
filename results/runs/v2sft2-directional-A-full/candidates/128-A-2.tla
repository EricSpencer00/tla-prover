---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
\* A value is any element of the specified constant set Values
Value == Values

\* The domain of the sequence is the set of indices 1..Len
Domain(s) == 1..Len(s)

\* An interval is a pair of indices [i, j] with i <= j
Interval == [i \in 1..Len(Seq) :-> j \in 1..Len(Seq) : (i <= j)]

\* A set of intervals is a finite set of Interval values
Intervals == { i \in Interval }

\* The work set is a set of intervals that still need processing
WorkSet == SUBSET Intervals

\* A permutation of the domain is a bijection from Domain(Seq) to itself
Permutation == { f \in [Domain(Seq) -> Domain(Seq)] : \A i \in Domain(Seq) : f[i] \in Domain(Seq) }

\* The predicate that a sequence s' is a valid partition of s over an interval [l, r] with pivot p
Partition(s, s', l, r, p) ==
    /\ l \in 1..Len(s) /\ r \in l..Len(s)
    /\ p \in l..r
    /\ \A i \in {1..l-1, r+1..Len(s)} : s'[i] = s[i]
    /\ \A i, j \in l..r :
          (i <= p /\ j > p) => s'[i] <= s'[j]
    /\ Unchanged(s, s', l, r, p) \* placeholder for more precise constraints

\* Unchanged ensures that elements outside the interval remain unchanged.
Unchanged(s, s', l, r, p) ==
    \A i \in 1..Len(s) : (i < l \/ i > r) => s'[i] = s[i]

\* A permutation of the domain that preserves values outside the interval
PermPreserve(s, s', l, r) ==
    \A i \in 1..Len(s) :
        (i < l \/ i > r) => s'[i] = s[i]
    /\ \A i \in l..r : s'[i] \in s[l..r]

\* -----------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------
VARIABLES SeqVal, Orig, Work, PC

\* -----------------------------------------------------------------
\* Constants (to be defined in the companion .cfg)
\* -----------------------------------------------------------------
\* Values - the set of permissible integer values
\* MaxSeqLen - the maximum allowed length of the sequence
\* Seq - the actual initial sequence (chosen nondeterministically)

\* -----------------------------------------------------------------
\* Types
\* -----------------------------------------------------------------
TypeOK ==
    /\ SeqVal \in [1..MaxSeqLen -> Value]
    /\ Orig \in [1..MaxSeqLen -> Value]
    /\ PC \in {"Main", "Terminate"}

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
    /\ SeqVal = Seq
    /\ Orig = Seq
    /\ Work = { [i |-> j] : (i \in 1..Len(Seq) /\ j \in i..Len(Seq)) }
    /\ PC = "Main"

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
Main ==
    /\ PC = "Main"
    /\ \E i \in Work :
        \E r, p \in DOMAIN(i) :
            /\ r \in DOMAIN(i)
            /\ p \in DOMAIN(i)
            /\ (\E pf \in Permutation :
                   /\ (* Left part *)
                      \A idx \in DOMAIN(i) :
                         (idx <= p) => pf[idx] <= pf[p]
                   /\ (* Right part *)
                      \A idx \in DOMAIN(i) :
                         (idx > p) => pf[p] <= pf[idx]
                   /\ (* Domain preservation *)
                      \A idx \in DOMAIN(i) : pf[idx] \in DOMAIN(i))
            /\ (* Update the sequence with a valid partition *)
            /\ SeqVal' = [SeqVal EXCEPT ![DOMAIN(i)] = [x \in DOMAIN(i) |-> SeqVal[pf[x]]]]
            /\ (* Update the work set *)
            /\ Work' = (Work \ {i}) \cup
                       { [l |-> p-1] : (p-1 >= DOMAIN(i)) } \cup
                       { [p+1 |-> r] : (p+1 <= DOMAIN(i)) }
            /\ PC' = "Main"

Terminate ==
    /\ PC = "Main"
    /\ Work = {}
    /\ PC' = "Terminate"
    /\ UNCHANGED SeqVal

Stutter ==
    /\ PC = "Terminate"
    /\ UNCHANGED <<SeqVal, Work, PC>>

Next ==
    \/ Main
    \/ Terminate
    \/ Stutter

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<SeqVal, Work, PC>>

\* -----------------------------------------------------------------
\* Safety invariants
\* -----------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ PC = "Terminate" => Sorted(SeqVal)

Sorted(s) ==
    \A i, j \in 1..Len(s) : (i <= j) => s[i] <= s[j]

PCorrect ==
    /\ PC = "Terminate"
    /\ PermPreserve(Orig, SeqVal, 1, Len(SeqVal))

\* -----------------------------------------------------------------
\* Liveness property (used in the .cfg)
\* -----------------------------------------------------------------
Termination ==
    WF_vars(Next)

\* -----------------------------------------------------------------
\* TLC specification
\* -----------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect

====