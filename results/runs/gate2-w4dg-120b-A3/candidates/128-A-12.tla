---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

ASSUME Values \subseteq Nat

RECURSIVE PermOf(_, _)
PermOf(f, S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
           y == CHOOSE z \in S : z # x
       IN {<<f[x], f[y]>>} \cup PermOf(f, S \ {x, y})

\* A partition leaves elements outside the interval untouched and forces
\* everything at or below the pivot index to be <= everything above it.
\* It is deliberately nondeterministic within those constraints.
VARIABLES seq, original, work, pc
vars == <<seq, original, work, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ original \in Seq(Values)
  /\ work \subseteq [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq \in {s \in Seq(Values) : Len(s) >= 1 /\ Len(s) <= MaxSeqLen}
  /\ original = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* A subinterval is empty if its high endpoint is below its low one.
InBounds(i, r) == r.lo <= i /\ i <= r.hi

PartitionsOf(s, r, i) ==
  {t \in {u \in Seq(Values) :
            /\ Len(u) = Len(s)
            /\ \A k \in 1..Len(s) : ~InBounds(k, r) => u[k] = s[k]
            /\ \A x \in 1..Len(s), y \in 1..Len(s) :
                 (InBounds(x, r) /\ InBounds(y, r) /\ x <= i /\ y > i) => u[x] <= u[y]}
   : \A k \in 1..Len(s) : k # i => u[k] = s[k]} \ {s}

Subintervals(r, i) ==
  {[lo |-> r.lo, hi |-> i], [lo |-> i + 1, hi |-> r.hi]}

SelectInterval ==
  \E r \in work :
    /\ work' = work \ {r}
    /\ IF r.lo = r.hi
         THEN work'
         ELSE \E i \in r.lo..r.hi :
                /\ seq' \in PartitionsOf(seq, r, i)
                /\ work' = work' \cup Subintervals(r, i)
    /\ pc' = IF work = {r} THEN "done" ELSE pc
    /\ UNCHANGED original

Next == SelectInterval

\* A stuttering step once termination is reached; needed for strong fairness.
Stall == /\ pc = "done" /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(SelectInterval) /\ [][Stall]_vars

\* The two halves are sorted internally and every element in the left half
\* is <= every element in the right half, so the whole sequence is sorted.
Inv ==
  /\ work \subseteq [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
  /\ Permutation(seq, original)
  /\ \A i, j \in 1..Len(seq) : (i < j) => seq[i] <= seq[j]

PCorrect == pc = "done" => Inv
Termination == <>(pc = "done")

\* The original finite-sequence operator is replaced by a bounded version
\* for model checking; extend the original definition so nobody has to
\* learn a new name.
LimitedSeq ==
  {\A s \in Seq(Values) : Len(s) <= MaxSeqLen : s}

====