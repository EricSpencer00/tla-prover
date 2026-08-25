---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Interval == [low : Nat, high : Nat]

\* permutation of a sequence (exists a bijection on indices)
Bijective(f) == 
    /\ \A i, j \in DOMAIN f : f[i] = f[j] => i = j
    /\ \A j \in DOMAIN f : \E i \in DOMAIN f : f[i] = j

Perm(s, t) == 
    \E f \in [DOMAIN s -> DOMAIN t] :
        /\ Bijective(f)
        /\ \A i \in DOMAIN s : t[i] = s[f[i]]

\* a partition of seq over interval int with pivot p
Partition(seq, int, p) == 
    { s2 \in LimitedSeq(Values) :
        /\ Len(s2) = Len(seq)
        /\ \A i \in 1..Len(seq) :
            (i < int.low \/ i > int.high) => s2[i] = seq[i]
        /\ \A i \in int.low..p :
            \A j \in p+1..int.high :
                s2[i] <= s2[j]
        /\ Perm(seq, s2)
    }

\* ----------------------------------------------------------------------
\* Type checking
\* ----------------------------------------------------------------------
TypeOK == 
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq { i \in Interval :
                        i.low <= i.high /\ 
                        i.low >= 1 /\ i.high <= Len(seq) }
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Invariant: permutation preservation and ordering between disjoint intervals
\* ----------------------------------------------------------------------
SortedBetween == 
    \A a, b \in work :
        (a.high < b.low) => 
            \A i \in a.low..a.high :
                \A j \in b.low..b.high :
                    seq[i] <= seq[j]

Inv == 
    /\ TypeOK
    /\ Perm(orig, seq)
    /\ SortedBetween

\* ----------------------------------------------------------------------
\* Definition of a sorted sequence
\* ----------------------------------------------------------------------
Sorted(s) == 
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, the sequence is sorted
\* ----------------------------------------------------------------------
PCorrect == pc = "Done" => (Sorted(seq) /\ Perm(orig, seq))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ seq \in LimitedSeq(Values)
    /\ orig = seq
    /\ work = { [low |-> 1, high |-> Len(seq)] }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E int \in work :
            /\ int.low = int.high
            /\ 
               /\ work' = work \ {int}
               /\ seq'  = seq
               /\ orig' = orig
               /\ pc'   = "Loop"
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E int \in work :
            /\ int.low < int.high
            /\ \E p \in int.low .. int.high :
                /\ \E s2 \in Partition(seq, int, p) :
                    /\ seq' = s2
                    /\ orig' = orig
                    /\ pc' = "Loop"
                    /\ work' = (work \ {int}) 
                               \cup (IF int.low <= p-1 
                                    THEN { [low |-> int.low, high |-> p-1] } 
                                    ELSE {}) 
                               \cup (IF p+1 <= int.high 
                                    THEN { [low |-> p+1, high |-> int.high] } 
                                    ELSE {})
    \/ /\ pc = "Loop"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====