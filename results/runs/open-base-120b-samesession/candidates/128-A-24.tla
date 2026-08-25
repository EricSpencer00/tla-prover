---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants required by the configuration file
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq for model checking
\* ----------------------------------------------------------------------
LimitedSeq ==
  { s \in Seq(Values) :
      /\ Len(s) <= MaxSeqLen
      /\ Len(s) > 0 }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Domain(seq) == 1 .. Len(seq)

Interval == [low : Nat, high : Nat]

Intervals(D) ==
  { [low |-> i, high |-> j] :
      i \in D /\ j \in D /\ i <= j }

Low(i) == i.low
High(i) == i.high

\* Subsequence of a sequence from positions l .. h (inclusive)
SubSeq(s, l, h) ==
  [i \in 1 .. (h - l + 1) |-> s[l + i - 1]]

\* Bijective function on a domain D
Bijective(f, D) ==
  /\ f \in [D -> D]
  /\ \A i, j \in D : f[i] = f[j] => i = j

\* Permutation predicate between two sequences of equal length
IsPermutation(s1, s2) ==
  LET D == Domain(s1) IN
    /\ Len(s1) = Len(s2)
    /\ \E f \in [D -> D] : Bijective(f, D) /\ \A i \in D : s1[i] = s2[f[i]]

\* Sortedness predicate (non‑decreasing order)
Sorted(s) ==
  \A i, j \in Domain(s) : i < j => s[i] <= s[j]

\* Partition operator: all possible results of a legal partition step
Partition(s, intv, p) ==
  { ns \in LimitedSeq :
      /\ Len(ns) = Len(s)
      /\ \A i \in Domain(s) :
           (i < Low(intv) \/ i > High(intv)) => ns[i] = s[i]
      /\ IsPermutation(SubSeq(ns, Low(intv), High(intv)),
                       SubSeq(s,  Low(intv), High(intv)))
      /\ \A i, j \in Low(intv) .. High(intv) :
           (i <= p /\ j > p) => ns[i] <= ns[j] }

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals(Domain(seq))
  /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Program‑counter correctness
\* ----------------------------------------------------------------------
PCorrect == pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Main invariant (partial‑correctness)
\* ----------------------------------------------------------------------
Inv ==
  /\ PCorrect
  /\ TypeOK
  /\ IF pc = "done"
        THEN /\ Sorted(seq)
             /\ IsPermutation(seq, orig)
        ELSE TRUE

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "run"

\* ----------------------------------------------------------------------
\* One iteration of the quicksort loop
\* ----------------------------------------------------------------------
Step ==
  \/ /\ pc = "run"
     /\ work # {}
     /\ \E intv \in work :
          LET l == Low(intv) IN
          LET h == High(intv) IN
            IF l = h
              THEN /\ work' = work \ {intv}
                   /\ UNCHANGED <<seq, orig, pc>>
            ELSE
              /\ \E p \in l .. h :
                    /\ \E ns \in Partition(seq, intv, p) :
                         /\ seq' = ns
                         /\ orig' = orig
                         /\ pc' = "run"
                         /\ work' = (work \ {intv}) \cup
                              (IF l <= p-1 THEN { [low |-> l, high |-> p-1] } ELSE {}) \cup
                              (IF p+1 <= h THEN { [low |-> p+1, high |-> h] } ELSE {})
           

  \/ /\ pc = "run"
     /\ work = {}
     /\ pc' = "done"
     /\ UNCHANGED <<seq, orig, work>>

  \/ /\ pc = "done"
     /\ UNCHANGED <<seq, orig, work, pc>>

Next == Step

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file
\* ----------------------------------------------------------------------
PCorrect == PCorrect
TypeOK   == TypeOK
Inv      == Inv

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

====