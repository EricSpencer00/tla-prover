---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* Required operator: this is the finite version of Sequences!Seq used by the
\* companion .cfg to keep the model bounded.  Seq is still in scope from
\* EXTENDS Sequences, but we do NOT redeclare it here.
LimitedSeq(S) == CHOOSE T \in Seq(S) : Len(T) <= MaxSeqLen

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

RECURSIVE IsSorted(_)
IsSorted(s) == Len(s) < 2 \/ (s[1] <= s[2] /\ IsSorted(Tail(s)))

\* A domain automorphism of a finite sequence domain.
Permutation(n) == {f \in [1..n -> 1..n] : \A x \in 1..n : \E! y \in 1..n : f[y] = x}

RECURSIVE Apply(_, _)
Apply(s, f) == IF Len(s) = 0 THEN <<>> ELSE <<s[f[1]]>> \o Apply(s, [i \in 1..(Len(s)-1) |-> f[i+1]])

\* The partition operator abstracts over the actual partitioning steps of
\* Quicksort: any sequence that preserves outside the interval and respects the
\* pivot ordering is a legal result.
Partition(s, i, j) ==
  {p \in Permutation(Len(s))
     : \A k \in 1..Len(s) : (k < i \/ k > j) => p[k] = k
          /\ (\A a \in i..j, b \in (j+1)..Len(s) : s[p[a]] <= s[p[b]])}

\* The algorithm keeps a copy of the original sequence so the final result can
\* be compared against it without mutating the input.
Domain == 1..Len(seq)

TypeOK ==
  /\ seq \in Seq(Values)
  /\ original \in Seq(Values)
  /\ work \subseteq [lo: Domain, hi: Domain]
  /\ pc \in {"loop", "done"}

Init ==
  /\ Len(seq) \in 1..MaxSeqLen /\ \E x \in (Values)^{1..MaxSeqLen} : seq = x
  /\ original = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

Step ==
  /\ pc = "loop"
  /\ \E w \in work :
       /\ work' = work \ {w}
       /\ IF w.lo = w.hi
            THEN work'
            ELSE
              \E k \in w.lo..w.hi :
                /\ seq' \in Partition(seq, w.lo, k)
                /\ work' = work' \cup {[lo |-> w.lo, hi |-> k], [lo |-> k+1, hi |-> w.hi]}
       /\ pc' = IF work' = {} THEN "done" ELSE "loop"

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Termination: the algorithm must always reach its terminal state.
Termination == <>(pc = "done")

PCorrect ==
  pc = "done" => (IsSorted(seq) /\ \E f \in Permutation(Len(original)) : seq = Apply(original, f))

Inv ==
  /\ work \subseteq [lo: Domain, hi: Domain]
  /\ \A a, b \in work : a.lo <= a.hi /\ b.lo <= b.hi
  /\ \A a \in work : \A x \in a.lo..a.hi, y \in (a.hi+1)..Len(seq) : seq[x] <= seq[y]
  /\ \A x \in 1..Len(seq) : \E f \in Permutation(Len(seq)) : seq[x] = original[f[x]]

TypeOKInv == TypeOK /\ Inv
====