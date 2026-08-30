---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A finite version of Seq that bounds the model; kept separate from the
\* imported Seq name so the .cfg replacement can apply to it.
LimitedSeq == [n \in Nat |-> {x \in Values : x \in 1..n}]

\* A partition of a sequence is any permutation of it that keeps elements
\* outside the interval fixed and leaves every below-pivot value no greater
\* than every above-pivot value -- that is exactly what a correct partition
\* routine would guarantee without being modelled here.
Partition(seq, lo, hi, p) ==
  {s \in Permutations(seq) : \A i \in 1..Len(seq) :
      (i < lo \/ i > hi \/ seq[i] \in Values) => s[i] = seq[i]}
   \cap {s \in Seq(Vals) : \A i \in lo..p, j \in (p+1)..hi :
      s[i] <= s[j]

RECURSIVE Permutations(_)
Permutations(seq) =
  IF seq = <<>> THEN {<<>>}
  ELSE {<<x>> \o s : s \in Permutations(Tail(seq)) /\ x \in Values}

RECURSIVE IsSorted(_)
IsSorted(seq) ==
  IF Len(seq) <= 1 THEN TRUE
  ELSE /\ seq[1] <= Head(Tail(seq))
     /\ IsSorted(Tail(seq))

\* The permutation check is the counting argument: each value appears the
\* same number of times in the original and the sorted sequence.
\* The relative sorting between adjacent intervals covers the whole range
\* once every interval is a singleton, which is what gives global sorting.
RECURSIVE CountIn(_)
CountIn(v, seq) ==
  IF seq = <<>> THEN 0
  ELSE (IF Head(seq) = v THEN 1 ELSE 0) + CountIn(v, Tail(seq))

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Interval == {in \in (1..MaxSeqLen) \X (1..MaxSeqLen) : in[1] <= in[2]}
Intervals == UNION {[1..n] : n \in 1..MaxSeqLen}

TypeOK ==
  /\ seq \in Seq(Vals)
  /\ orig \in Seq(Vals)
  /\ work \in SUBSET Interval
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] : seq = s
  /\ orig = seq
  /\ work = {[1..MaxSeqLen]}
  /\ pc = "loop"

Loop ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E in \in work :
       /\ (in[1] = in[2] \/ \E p \in in[1]..in[2] :
            /\ seq' \in Partition(seq, in[1], in[2], p)
            /\ work' = (work \ {in}) \cup {[in[1] .. p], [p+1 .. in[2]]})
       /\ pc' \in {"loop", "done"}
       /\ orig' = orig

Done ==
  /\ pc = "done"
  /\ work = {}
  /\ pc' = pc
  /\ UNCHANGED <<seq, orig, work>>

Next == Loop \/ Done

\* Weak fairness on the loop body is enough once "done" is reachable.
Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

PCorrect ==
  /\ \A v \in Values : CountIn(v, orig) = CountIn(v, seq)
  /\ IsSorted(seq)

\* The domain partition is exactly the whole sequence once every interval
\* has been refined to a point.
DomainPartitioned ==
  \A i \in Intervals : \E in \in work : i \in in

Permutation == \A v \in Values : CountIn(v, orig) = CountIn(v, seq)

RelativeSortedness ==
  \A in \in work :
    \A i \in in[1]..(in[2] - 1) : seq[i] <= seq[i+1]

Inv == PCorrect /\ DomainPartitioned /\ Permutation /\ RelativeSortedness

Termination == <>(pc = "done")

====