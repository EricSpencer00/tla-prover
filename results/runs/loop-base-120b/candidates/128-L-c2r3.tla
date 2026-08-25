---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* A finite version of Seq for model checking
\* ----------------------------------------------------------------------
\* Sequences.Seq(V) is the set of all finite sequences over V.
\* LimitedSeq restricts the length to be at most MaxSeqLen.
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

vars == << seq, orig, work, pc >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Predicate indicating that a tuple I is a valid interval of seq
Interval(I) == 
    /\ I \in (1..Len(seq)) \X (1..Len(seq))
    /\ I[1] <= I[2]

\* The set of all intervals (used only for typing)
AllIntervals == { I \in (1..Len(seq)) \X (1..Len(seq)) : I[1] <= I[2] }

\* Extract the lower and upper sub‑intervals given a pivot p in interval I
LowerSub(I, p) == << I[1], p >>
UpperSub(I, p) == << p+1, I[2] >>

\* Length of an interval
IntervalLen(I) == I[2] - I[1] + 1

\* Count occurrences of a value v in a sequence s
Count(s, v) == Cardinality({ i \in DOMAIN(s) : s[i] = v })

\* Permutation predicate (multiset equality)
Permutation(s, t) == 
    \A v \in Values : Count(s, v) = Count(t, v)

\* Sortedness predicate (non‑decreasing order)
Sorted(s) == 
    \A i, j \in DOMAIN(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ seq \in LimitedSeq
    /\ orig \in LimitedSeq
    /\ Len(seq) = Len(orig)
    /\ work \subseteq AllIntervals
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Main invariant (preserves permutation)
\* ----------------------------------------------------------------------
Inv == 
    /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated the result is sorted and a
\* permutation of the original input
\* ----------------------------------------------------------------------
PCorrect == 
    (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ \E s \in LimitedSeq :
          /\ Len(s) # 0
          /\ seq = s
          /\ orig = s
          /\ work = { <<1, Len(s)>> }
          /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* The main transition relation
\* ----------------------------------------------------------------------
Next == 
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E I \in work :
            LET i == I[1] IN
            LET j == I[2] IN
            IF i = j THEN
                /\ work' = work \ {I}
                /\ UNCHANGED <<seq, orig, pc>>
            ELSE
                /\ \E p \in i..j :
                       LET lower == LowerSub(I, p) IN
                       LET upper == UpperSub(I, p) IN
                       /\ lower[1] <= lower[2]    \* lower non‑empty
                       /\ upper[1] <= upper[2]    \* upper non‑empty (might be empty when p=j)
                       /\ \E sNew \in LimitedSeq :
                              /\ Len(sNew) = Len(seq)
                              /\ \A k \in DOMAIN(seq) :
                                    IF k \in i..j THEN
                                        ( (k <= p) => \A m \in p+1..j : sNew[k] <= sNew[m] )
                                        /\ ( (k > p) => \A m \in i..p : sNew[m] <= sNew[k] )
                                    ELSE
                                        sNew[k] = seq[k]
                              /\ seq' = sNew
                       /\ work' = (work \ {I}) \cup {lower, upper}
                       /\ UNCHANGED orig
                       /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants for model checking
\* ----------------------------------------------------------------------
PCorrectInv == PCorrect
TypeOKInv    == TypeOK
MainInv      == Inv

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")
====