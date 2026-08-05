---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Permutations

CONSTANTS Values, MaxSeqLen

\* LimitedSeq is a finite-depth version of the Seq operator from
\* Sequences: it only builds sequences up to MaxSeqLen, so the model stays
\* checkable.  It is declared as an operator here because the .cfg replaces
\* the name Seq from the imported module with it.
LimitedSeq ==
  LET F[i \in 1..MaxSeqLen] == IF i = 1 THEN {Values} ELSE {Values} \cup {x \circ y : x \in F[i - 1], y \in Values}
  IN F[MaxSeqLen]

RECURSIVE At(_,_)
At(s, i) == IF i = Len(s) THEN s[i] ELSE s[i] \circ At(s, i + 1)

PermutationSeq(s, t) ==
  /\ Len(s) = Len(t)
  /\ \E f \in Automorphisms(Len(s)) : t = At(s, f[1]) \circ At(s, f[2]) \circ ... \circ At(s, f[Len(s)])

\* A partition of s over [b..e] around pivot p is any permutation of the
\* segment s[b..e] that puts every element at or below p no greater than
\* every element above p; elements outside the segment are untouched.
Partition(s, b, e, p) ==
  let seg == s[b] \circ s[b + 1] \circ ... \circ s[e]
      lower == {x \in seg : x <= p}
      upper == {x \in seg : x >= p}
  in { t \in (Seq(Lower) \cup Seq(Upper)) : PermutationSeq(seg, t) }

\* An interval is an inclusive range of indices in the current sequence.
Interval == {i \in 1..MaxSeqLen}

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ work \subseteq [low : Interval, high : Interval]
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq \in LimitedSeq
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = {[low |-> 1, high |-> Len(seq)]}
  /\ pc = "loop"

\* One Quicksort iteration: pick an interval, either discard a singleton or
\* partition it around a pivot and replace it with two subintervals.
Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E it \in work :
       /\ LET lower == [low |-> it.low, high |-> it.high - 1]
              upper == [low |-> it.high + 1, high |-> it.high]
          IN
          IF it.low = it.high THEN work' = work \ {it}
          ELSE
            /\ \E p \in Values :
                 /\ \E s' \in Partition(seq, it.low, it.high, p) :
                      /\ seq' = s'
                      /\ work' = (work \ {it}) \cup {lower, upper}
  /\ pc' = "loop"

Terminating ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminating \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

PCorrect == pc = "done" => (PermutationSeq(orig, seq) /\ \A i \in 1..Len(seq) - 1 : seq[i] <= seq[i + 1])

\* The invariant is a three-way conjunction: (1) the low/high fields of
\* every interval stay inside the sequence's domain, (2) every index of
\* the sequence is covered by exactly one interval, and (3) the maximum
\* element of a lower interval is never greater than the minimum of the
\* interval immediately above it (pairwise relative ordering).
Inv ==
  /\ \A it \in work : it.low <= it.high /\ it.high <= Len(seq)
  /\ \A i \in 1..Len(seq) :
       \E it \in work :
         /\ i >= it.low
         /\ i <= it.high
         /\ \A jt \in work : i >= jt.low /\ i <= jt.high => jt = it
  /\ \A it \in work, jt \in work :
       it.low < jt.low /\ it.high < jt.low =>
         /\ \E i \in it.low..it.high : \E j \in jt.low..jt.high : seq[i] <= seq[j]

Termination == (pc = "loop") ~> (pc = "done")

====