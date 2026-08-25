---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\*--------------------------------------------------------------------
\* A finite version of Seq for model checking (replaces Seq in .cfg)
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Indices(seq) == 1 .. Len(seq)

Interval == <<l, h>> \* l and h are natural numbers with l <= h

Intervals == { <<l, h>> \in Seq(Nat) :
                 l \in Indices(seq) /\ h \in Indices(seq) /\ l <= h }

\* Count of a value v in a sequence
Count(s, v) == Cardinality({ i \in Indices(s) : s[i] = v })

\* Two sequences are permutations of each other (multiset equality)
IsPermutation(s, t) == 
    /\ Len(s) = Len(t)
    /\ \A v \in Values : Count(s, v) = Count(t, v)

\* Sub‑sequence from l to h (inclusive)
SubSeq(s, l, h) ==
    [ i \in 1 .. (h - l + 1) |-> s[l + i - 1] ]

\* Sortedness predicate
Sorted(s) == \A i, j \in Indices(s) : i < j => s[i] <= s[j]

\* Partition predicate (the new sequence must be a valid partition)
PartitionValid(old, new, l, h, p) ==
    /\ Len(old) = Len(new)
    /\ (\A i \in Indices(old) :
          (i < l \/ i > h) => new[i] = old[i])
    /\ (\A i \in l .. p-1 : new[i] <= new[p])
    /\ (\A i \in p+1 .. h : new[i] >= new[p])
    /\ IsPermutation(SubSeq(old, l, h), SubSeq(new, l, h))

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\*--------------------------------------------------------------------
\* Main step: process an interval
\*--------------------------------------------------------------------
Process ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E int \in work :
          LET l == int[1] IN
          LET h == int[2] IN
          IF l = h THEN
              /\ work' = work \ {int}
              /\ seq' = seq
          ELSE
              /\ \E p \in l .. h :
                     /\ \E newSeq \in LimitedSeq(Values) :
                            /\ Len(newSeq) = Len(seq)
                            /\ PartitionValid(seq, newSeq, l, h, p)
                     /\ seq' = newSeq
              /\ work' = (work \ {int})
                        \cup (IF l <= p-1 THEN {<<l, p-1>>} ELSE {})
                        \cup (IF p+1 <= h THEN {<<p+1, h>>} ELSE {})
          /\ orig' = orig
          /\ pc' = "Loop"

\*--------------------------------------------------------------------
\* Termination step: work set empty
\*--------------------------------------------------------------------
Terminate ==
    /\ pc = "Loop"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

\*--------------------------------------------------------------------
\* Stuttering after termination (prevents deadlock)
\*--------------------------------------------------------------------
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next == Process \/ Terminate \/ Stutter

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
vars == <<seq, orig, work, pc>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq Intervals
    /\ pc \in {"Loop", "Done"}

Inv == TypeOK /\ IsPermutation(seq, orig)

PCorrect == (pc = "Done") => Sorted(seq)

\*--------------------------------------------------------------------
\* Liveness property
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")

\*--------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\*--------------------------------------------------------------------
SPECIFICATION Spec
INVARIANT PCorrect
INVARIANT TypeOK
INVARIANT Inv
PROPERTY Termination

====