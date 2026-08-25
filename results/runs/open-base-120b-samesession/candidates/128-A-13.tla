---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets, TLC

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*--------------------------------------------------------------------
\* Operator that replaces Seq from the standard Sequences module.
\* It restricts sequences to length at most MaxSeqLen.
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
\* Interval is a 2‑element sequence <<low, high>> with 1 ≤ low ≤ high ≤ Len(seq)
IsInterval(I) == 
    /\ I \in Seq(Nat) 
    /\ Len(I) = 2
    /\ LET low == I[1], high == I[2] IN
       /\ 1 <= low
       /\ low <= high
       /\ high <= Len(seq)

\* Set of all possible intervals for the current sequence length
INTERVALS == { I \in Seq(Nat) : IsInterval(I) }

\* Bag (multiset) of values of a sequence on a given index range
Bag(s, lo, hi) ==
    [v \in Values |-> 
        Cardinality({ i \in lo..hi : s[i] = v })]

\* Global permutation predicate
Permutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ Bag(s1, 1, Len(s1)) = Bag(s2, 1, Len(s2))

\* Sortedness on a closed index interval
SortedOn(s, lo, hi) ==
    /\ lo >= hi \/ \A i, j \in lo..hi : i < j => s[i] <= s[j]

\* Set of sequences that represent a valid partition of seq over [lo..hi] with pivot
Partition(seq, lo, hi, pivot) ==
    { s' \in LimitedSeq(Values) :
        /\ Len(s') = Len(seq)
        /\ \A i \in 1..Len(seq) :
              (i < lo \/ i > hi) => s'[i] = seq[i]
        /\ \A i \in lo..pivot, j \in pivot+1..hi : s'[i] <= s'[j]
        /\ Bag(s', lo, hi) = Bag(seq, lo, hi) }

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ seq # <<>>
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
    \/ /\ work # {}
       /\ \E I \in work :
            LET low  == I[1] ,
                high == I[2] 
            IN
            IF low = high THEN
                /\ work' = work \ {I}
                /\ UNCHANGED <<seq, orig, pc>>
            ELSE
                /\ \E pivot \in low..high :
                       LET lo1  == low
                           hi1  == pivot - 1
                           lo2  == pivot + 1
                           hi2  == high
                       IN
                       /\ \E newSeq \in Partition(seq, low, high, pivot) :
                              /\ seq' = newSeq
                              /\ work' = (work \ {I}) 
                                        \cup (IF lo1 <= hi1 THEN {<<lo1, hi1>>} ELSE {})
                                        \cup (IF lo2 <= hi2 THEN {<<lo2, hi2>>} ELSE {})
                              /\ pc' = "Loop"
                /\ UNCHANGED orig
            END IF
    \/ /\ work = {}
       /\ pc = "Loop"
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED vars

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq INTERVALS
    /\ pc \in {"Loop", "Done"}

\* Global permutation and sortedness for intervals already removed from work
Inv ==
    /\ TypeOK
    /\ Permutation(seq, orig)
    /\ \A I \in INTERVALS \ work :
          SortedOn(seq, I[1], I[2])

\* When the algorithm has terminated, the whole sequence is sorted
PCorrect ==
    (pc = "Done") => (Permutation(seq, orig) /\ SortedOn(seq, 1, Len(seq)))

\*--------------------------------------------------------------------
\* Liveness property (termination)
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")

====