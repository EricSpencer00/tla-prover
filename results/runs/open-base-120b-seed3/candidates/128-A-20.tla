---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq for model checking
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Intervals are represented as a pair <<lo, hi>> with 1 ≤ lo ≤ hi ≤ Len(seq)
\* ----------------------------------------------------------------------
Interval == <<lo, hi>> \in Seq(Nat)

AllIntervals == { <<lo, hi>> \in Seq(Nat) :
                     1 <= lo /\ lo <= hi /\ hi <= Len(seq) }

\* ----------------------------------------------------------------------
\* Permutation predicate (multiset equality)
\* ----------------------------------------------------------------------
Permutation(s, t) ==
    /\ Len(s) = Len(t)
    /\ \A x \in Values : 
         Cardinality({ i \in 1..Len(s) : s[i] = x }) =
         Cardinality({ i \in 1..Len(t) : t[i] = x })

\* ----------------------------------------------------------------------
\* Sorted predicate
\* ----------------------------------------------------------------------
Sorted(s) ==
    /\ Len(s) = 0 \/ Len(s) = 1
       => TRUE
    /\ \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig \in LimitedSeq(Values) /\ Len(orig) = Len(seq)
    /\ work \subseteq AllIntervals
    /\ pc \in {"Loop", "Done"}
    /\ \A i \in 1..Len(seq) : seq[i] \in Values
    /\ \A i \in 1..Len(orig) : orig[i] \in Values

\* ----------------------------------------------------------------------
\* General invariant used in the proof
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial‑correctness condition (when the algorithm terminates)
\* ----------------------------------------------------------------------
PCorrect ==
    pc = "Done" => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \E s \in LimitedSeq(Values) : Len(s) > 0 /\ 
          /\ seq' = s
          /\ orig' = s
    /\ seq' = seq
    /\ orig' = orig
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"
    /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Main step of the algorithm
\* ----------------------------------------------------------------------
PartitionStep ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E I \in work :
          LET lo  == I[1] IN
          LET hi  == I[2] IN
          /\ IF lo = hi THEN
                (* singleton interval – just remove it *)
                /\ work' = work \ {I}
                /\ UNCHANGED <<seq, orig, pc>>
             ELSE
                (* non‑singleton interval – partition it *)
                /\ \E p \in lo..hi :
                      LET lower == <<lo, p-1>> IN
                      LET upper == <<p+1, hi>> IN
                      /\ \E s' \in LimitedSeq(Values) :
                            /\ Len(s') = Len(seq)
                            /\ (\A i \in 1..Len(seq) :
                                   (i < lo \/ i > hi) => s'[i] = seq[i])
                            /\ (\A i \in lo..p : s'[i] <= s'[p])
                            /\ (\A i \in p+1..hi : s'[i] >= s'[p])
                            /\ Permutation(s', seq)
                      /\ seq' = s'
                      /\ work' = (work \ {I})
                               \cup (IF lo <= p-1 THEN {lower} ELSE {})
                               \cup (IF p+1 <= hi THEN {upper} ELSE {})
                      /\ pc' = "Loop"
          )
    /\ UNCHANGED orig

TerminateStep ==
    /\ pc = "Loop"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

StutterAfterDone ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
    PartitionStep \/ TerminateStep \/ StutterAfterDone

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
PCorrect == PCorrect
TypeOK   == TypeOK
Inv      == Inv

Termination == <> (pc = "Done")

====