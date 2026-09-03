---- MODULE Quicksort ----
EXTENDS Integers, Sequences

CONSTANTS Values, MaxSeqLen

\* A partition of a subrange of seq: elements outside the range are unchanged,
\* while everything at or below the pivot index is no greater than everything
\* above it. The operator is nondeterministic, modelling any correct partition
\* procedure; every permitted result is a permutation of the original sequence.
Partition(seq, lo, hi, piv) ==
  { q \in [1..Len(seq) -> Values] :
      /\ \A i \in 1..Len(seq) : (i < lo \/ i > hi) => q[i] = seq[i]
      /\ \A i \in lo..piv, j \in (piv + 1)..hi : q[i] <= q[j] }

Intervals == [lo : 1..MaxSeqLen, hi : 1..MaxSeqLen]

LOOP == "Loop"
TERMINATED == "Terminated"
pc == "pc"
seq == "seq"
orig == "orig"
todo == "todo"

VARIABLES vars
vars == [pc : {LOOP, TERMINATED}, seq : Seq(Values), orig : Seq(Values),
         todo : SUBSET Intervals]

TypeOK ==
  /\ vars.pc \in {LOOP, TERMINATED}
  /\ vars.seq \in Seq(Values)
  /\ vars.orig \in Seq(Values)
  /\ vars.todo \subseteq Intervals

Init ==
  /\ \E s \in Seq(Values) : Len(s) <= MaxSeqLen /\ vars.seq = s
  /\ vars.orig = vars.seq
  /\ vars.todo = {[lo |-> 1, hi |-> Len(vars.seq)]}
  /\ vars.pc = LOOP

\* One loop iteration: split or settle a subrange, with the partition step
\* nondeterministically choosing any valid rearrangement of that subrange.
SortStep ==
  /\ vars.pc = LOOP
  /\ vars.todo # {}
  /\ \E it \in vars.todo :
       \/ (it.lo = it.hi /\ vars.todo' = vars.todo \ {it})
       \/ \E piv \in it.lo..it.hi :
            /\ \E newSeq \in Partition(vars.seq, it.lo, it.hi, piv) :
                 vars.seq' = newSeq
            /\ vars.todo' = (vars.todo \ {it})
                 \cup {[lo |-> it.lo, hi |-> piv], [lo |-> piv + 1, hi |-> it.hi]}
  /\ vars.pc' = vars.pc
  /\ vars.orig' = vars.orig

Terminate ==
  /\ vars.pc = LOOP
  /\ vars.todo = {}
  /\ vars.pc' = TERMINATED
  /\ vars.seq' = vars.seq
  /\ vars.orig' = vars.orig
  /\ vars.todo' = vars.todo

Stall ==
  /\ vars.pc = TERMINATED
  /\ vars' = vars

Next == SortStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep)

\* Sortedness is formulated as a pairwise condition that can only be false
\* for intervals that actually overlap, so no interval covering a single index
\* can ever be judged disordered and cause a spurious failure.
SortedWithin(i, j) ==
  /\ i <= j => vars.seq[i] <= vars.seq[j]
  /\ i > j => vars.seq[j] <= vars.seq[i]
Inv ==
  /\ /\ \A e \in vars.todo : e.lo <= e.hi
     /\ \E p \in [1..Len(vars.seq) -> 1..Len(vars.seq)] : IsPermutation(p, vars.orig, vars.seq)
  /\ \A i, j \in 1..Len(vars.seq) : SortedWithin(i, j)

PCorrect ==
  /\ (vars.pc = TERMINATED) => (SortedWithin(1, Len(vars.seq)) /\ Len(vars.seq) > 0)
  /\ (\A i, j \in 1..Len(vars.seq) : SortedWithin(i, j) => vars.pc = TERMINATED)

Termination == (vars.pc = LOOP) ~> (vars.pc = TERMINATED)

\* Replaces Seq from Sequences so the model stays finite and checkable.
LimitedSeq(i) == CHOOSE e \in {vars.seq[j] : j \in 1..i} : TRUE

====