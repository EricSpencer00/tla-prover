---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Constants (provided by the accompanying .cfg)
\* -------------------------------------------------
CONSTANT Values          \* Set of admissible integer values
CONSTANT MaxSeqLen       \* Upper bound on the length of the sequence
CONSTANT Seq             \* A nondeterministically chosen initial sequence

\* -------------------------------------------------
\* Derived sets
\* -------------------------------------------------
Indices == 1 .. Len(Seq)

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES seq, origSeq, work, pc

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
\* An interval is represented as a pair <<i, j>> with i <= j.
Interval == [i : Nat, j : Nat] \* i <= j will be enforced where needed

\* Initial work set contains the whole index range as a single interval
InitWork == { [i |-> 1, j |-> Len(seq)] }

\* A permutation of a sequence (bijection on indices)
Permutation(p) == 
    /\ p \in [1..Len(seq) -> 1..Len(seq)]
    /\ \A i, j \in 1..Len(seq) : p[i] = p[j] => i = j

\* Apply a permutation to a sequence
ApplyPerm(s, p) == 
    [i \in 1..Len(s) |-> s[p[i]]]

\* isPermutation(s, t) holds iff there exists a permutation p such that t = ApplyPerm(s, p)
IsPermutation(s, t) == 
    \E p \in [1..Len(s) -> 1..Len(s)] :
        /\ (\A i, j \in 1..Len(s) : p[i] = p[j] => i = j)
        /\ t = ApplyPerm(s, p)

\* Sortedness predicate (non‑decreasing order)
Sorted(s) == 
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ seq = Seq
    /\ origSeq = Seq
    /\ work = InitWork
    /\ pc = "Loop"

\* -------------------------------------------------
\* Partition step (abstract, nondeterministic)
\* -------------------------------------------------
Partition(s, interval, pivot) ==
    LET low  == interval.i
        high == interval.j
        pivotVal == s[pivot] IN
    \E sNew \in [1..Len(s) -> Values] :
        /\ \A k \in 1..Len(s) :
               (k < low \/ k > high) => sNew[k] = s[k]   \* unchanged outside interval
        /\ \A k \in low..pivot   : sNew[k] <= pivotVal
        /\ \A k \in pivot+1..high : sNew[k] >= pivotVal
        /\ IsPermutation(s, sNew)

\* -------------------------------------------------
\* One iteration of the main loop
\* -------------------------------------------------
LoopStep ==
    /\ pc = "Loop"
    /\ IF work = {} THEN
          /\ pc' = "Done"
          /\ UNCHANGED <<seq, origSeq, work>>
       ELSE
          /\ \E interval \in work :
                LET low  == interval.i
                    high == interval.j IN
                IF low = high THEN
                    /\ work' = work \ {interval}
                    /\ UNCHANGED <<seq, origSeq>>
                ELSE
                    /\ \E pivot \in low..high :
                        /\ Partition(seq, interval, pivot) = seq'
                        /\ work' = (work \ {interval}) \cup
                                   { [i |-> low,  j |-> pivot],
                                     [i |-> pivot+1, j |-> high] }
                /\ pc' = "Loop"
          /\ UNCHANGED origSeq

\* Stuttering step after termination
DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, origSeq, work, pc>>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next == LoopStep \/ DoneStutter

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

\* -------------------------------------------------
\* Invariant: type correctness (optional but useful)
\* -------------------------------------------------
TypeOK ==
    /\ seq \in [1..MaxSeqLen -> Values] 
    /\ origSeq \in [1..MaxSeqLen -> Values]
    /\ work \subseteq { [i |-> iNat, j |-> jNat] :
                        iNat \in 1..MaxSeqLen /\ 
                        jNat \in iNat..MaxSeqLen }
    /\ pc \in {"Loop", "Done"}

\* -------------------------------------------------
\* Invariant: permutation preservation
\* -------------------------------------------------
Inv ==
    /\ IsPermutation(origSeq, seq)
    /\ \A interval \in work :
          /\ interval.i >= 1 /\ interval.j <= Len(seq)
          /\ interval.i <= interval.j

\* -------------------------------------------------
\* Safety property (partial correctness)
\* -------------------------------------------------
PCorrect ==
    (pc = "Done") => /\ Sorted(seq)
                     /\ IsPermutation(origSeq, seq)

\* -------------------------------------------------
\* Liveness property (termination)
\* -------------------------------------------------
Termination == <>[](pc = "Done")

\* -------------------------------------------------
\* THEOREM statements (optional, for TLAPS)
\* -------------------------------------------------
THEOREM Spec => [](PCorrect)
THEOREM Spec => []Inv
THEOREM Spec => []TypeOK

====