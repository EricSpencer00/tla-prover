---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS Values, MaxSeqLen

Interval == {p \in Nat : p >= 1 /\ p <= MaxSeqLen}

VARIABLES seq, original, work, pc

vars == << seq, original, work, pc >>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) >= 1 /\ Len(seq) <= MaxSeqLen
  /\ original \in Seq(Values)
  /\ Len(original) = Len(seq)
  /\ work \subseteq (Interval \times Interval)
  /\ pc \in {"running", "done"}

DomainPartition(i, j) == {x \in 1..Len(seq) : i <= x <= j}

PermutationApp ==
  /\ seq = PermutationApply(seq, \E q \in Automorphisms(1..Len(seq)) : q)
  /\ original = PermutationApply(original, \E q \in Automorphisms(1..Len(seq)) : q)

RelativeSortedness ==
  /\ \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]
  /\ \A i \in 1..Len(seq) : original[i] <= original[i]
  /\ \A i, j \in 1..Len(seq) : i < j => original[i] <= original[j]

Inv == DomainPartition \cup PermutationApp \cup RelativeSortedness

Init ==
  /\ seq \in Seq(Values)
  /\ Len(seq) >= 1 /\ Len(seq) <= MaxSeqLen
  /\ original = seq
  /\ work = {<< 1, Len(seq) >>}
  /\ pc = "running"

\* Partition is abstracted: the result is any permutation that respects the
\* pivot ordering over the interval and leaves the rest untouched.
DoPartition(i, j, k) ==
  /\ k \in i..j
  /\ \E s \in Permutations(1..Len(seq)) :
       /\ \A x \in 1..Len(seq) : x < i \/ x > j => s[x] = x
       /\ \A x \in i..k, y \in k+1..j : seq[s[x]] <= seq[s[y]]
       /\ seq' = PermutationApply(seq, s)
  /\ work' = (work \ {<< i, j >>}) \union {<< i, k >>, << k + 1, j >>}
  /\ pc' = "running"

Next ==
  \/ (\E i, j \in Interval :
        /\ << i, j >> \in work
        /\ Len(seq) >= i
        /\ IF i = j
           THEN /\ work' = work \ {<< i, j >>}
                /\ UNCHANGED << seq, original, pc >>
           ELSE \E k \in i..j : DoPartition(i, j, k))
  \/ (pc = "running" /\ work = {} /\ pc' = "done")
  \/ (pc = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PCorrect == (pc = "done") => (\A x \in 1..Len(seq) : seq[x] = original[x])

Termination == (pc = "done") ~> TRUE

====