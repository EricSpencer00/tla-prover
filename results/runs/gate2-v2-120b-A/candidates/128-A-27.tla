---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANT Values      \* a finite subset of Nat (or Int) given by the cfg
CONSTANT MaxSeqLen   \* a positive integer bound on sequence length
CONSTANT Seq         \* the initial sequence (a non‑empty sequence over Values)

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Idx == 1..MaxSeqLen
Intervals == SUBSET [lo: Idx, hi: Idx]  \* intervals are pairs with lo ≤ hi

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SequenceIndices == { i \in Idx : i <= Len(seq) }

\* An interval is represented as a record with fields lo and hi.
Interval(lo, hi) == [lo |-> lo, hi |-> hi]

Sorted(s) ==
  \A i, j \in 1..Len(s) :
    (i < j) => s[i] <= s[j]

Permutes(s, t) ==
  \E f \in [1..Len(s) -> 1..Len(s)] :
    ( \A i, j \in 1..Len(s) : f[i] = f[j] => i = j ) /\   \* f is a bijection
    \A i \in 1..Len(s) : s[f[i]] = t[i]

\* ----------------------------------------------------------------------
\* Partition operator (abstract, nondeterministic)
\* ----------------------------------------------------------------------
Partition(seqIn, lo, hi, p) ==
  { seqOut \in Sequences(Seq) :
        Len(seqOut) = Len(seqIn) /\
        (\A i \in 1..Len(seqIn) :
            (i < lo) \/ (i > hi) => seqOut[i] = seqIn[i]) /\
        \E k \in lo..hi :
            /\ seqOut[p] = seqIn[k]                 \* pivot value stays somewhere in the interval
            /\ (\A i \in lo..p   : seqOut[i] <= seqOut[p]) /\
            /\ (\A i \in p+1..hi : seqOut[i] >= seqOut[p]) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq   = Seq
  /\ orig  = Seq
  /\ work  = { Interval(1, Len(Seq)) }
  /\ pc    = "Loop"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Terminate ==
  /\ work = {}
  /\ pc = "Done"

LoopStep ==
  /\ pc = "Loop"
  /\ LET I == CHOOSE i \in work : TRUE IN
     /\ IF I.lo = I.hi THEN
          /\ work' = work \ {I}
          /\ UNCHANGED << seq, orig, pc >>
        ELSE
          /\ \E p \in I.lo..I.hi :
               /\ \E seq' \in Partition(seq, I.lo, I.hi, p) :
                    /\ seq' # seq                \* must make progress
                    /\ seq' \in Sequences(Values)
          /\ \E p \in I.lo..I.hi, seq' \in Partition(seq, I.lo, I.hi, p) :
               /\ seq' \in Sequences(Values)
               /\ LET lowInt  == Interval(I.lo, p)
                     highInt == Interval(p+1, I.hi)
               IN /\ work' = (work \ {I}) \cup {lowInt, highInt}
                  /\ seq' = seq'
                  /\ UNCHANGED orig
          /\ pc' = "Loop"

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED << seq, orig, work, pc >>

Next ==
  \/ LoopStep
  \/ Terminate
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
PCorrect ==
  pc = "Done" => Seq = seq

TypeOK ==
  /\ seq \in Sequences(Values)
  /\ orig \in Sequences(Values)
  /\ work \subseteq { Interval(lo, hi) : lo, hi \in Idx, lo <= hi, hi <= Len(seq) }

Inv ==
  /\ Permutes(orig, seq)
  /\ Sorted(seq)

\* ----------------------------------------------------------------------
\* Safety property (partial correctness)
\* ----------------------------------------------------------------------
Termination ==
  []<>(pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREM (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

====