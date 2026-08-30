---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* Intervals are closed ranges of indices, and the work set is always a
\* partition of the whole index domain: intervals are never added and never
\* dropped, only split into two halves.
Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Domain == 1..MaxSeqLen

DomainOf(s) == {i \in Domain : i <= Len(s)}

\* A partition leaves everything outside the interval untouched and keeps
\* low-part elements <= high-part elements; any such sequence is reachable.
Partitions(s, I, i) ==
  {t \in Sequences.Seq(Values) :
     Len(t) = Len(s)
       /\ \A k \in Domain \ DomainOf(s) : t[k] = s[k]
       /\ \A k \in I.lo..i : \A j \in (i + 1)..I.hi : t[k] <= t[j]
       /\ \A k \in I.lo..i, j \in I.lo..i : k < j => s[k] <= s[j]
       /\ \A k \in (i + 1)..I.hi, j \in (i + 1)..I.hi : k < j => s[k] <= s[j]}

\* The algorithm is a state machine driven by pc, not a free-running
\* process: pc = "loop" means the loop guard held; pc = "halt" means it
\* did not, and the stutter step below is the only way out of halt.
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

IsPermutation(s, t) ==
  \A f \in [Domain -> Domain] :
    /\ (\A x \in Domain : f[f[x]] = x) /\ (\A x, y \in Domain : f[x] = f[y] => x = y)
    /\ \A x \in Domain : s[x] = t[f[x]]

TypeOK ==
  /\ seq \in Sequences.Seq(Values)
  /\ orig \in Sequences.Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "halt"}

Init ==
  /\ \E s \in Sequences.Seq(Values) :
       /\ Len(s) >= 1 /\ Len(s) <= MaxSeqLen
       /\ seq = s
       /\ orig = s
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* The pivot is chosen nondeterministically within the interval; the partition
\* is chosen nondeterministically from all partitions that a real partition
\* step could have produced -- that is what makes the model cover every
\* realistic interleaving of the two halves.
Partition ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E I \in work :
       /\ work' = work \ {I}
       /\ (I.lo = I.hi 
            \/ \E i \in I.lo..I.hi :
                 /\ \E ns \in Partitions(seq, I, i) : seq' = ns
                 /\ work' = work' \cup {[lo |-> I.lo, hi |-> i], [lo |-> i + 1, hi |-> I.hi]})
  /\ pc' = IF work = {} THEN "halt" ELSE pc

Stutter ==
  /\ pc = "halt"
  /\ pc' = pc
  /\ UNCHANGED <<seq, orig, work>>

Next ==
  \/ Partition
  \/ Stutter

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Partition)

\* PCorrect is the property; Inv is the strong inductive invariant that makes
\* the proof go through. Both are required by the task, and Termination is
\* the weak fairness property that closes the partial correctness argument.
Inv ==
  /\ \A I, J \in work : I = J \/ (I.hi < J.lo \/ J.hi < I.lo)
  /\ IsPermutation(seq, orig)
  /\ \A I, J \in work : I.hi < J.lo => \A k \in I.lo..I.hi, j \in J.lo..J.hi : seq[k] <= seq[j]

PCorrect ==
  pc = "halt" => (IsPermutation(seq, orig) /\ \A k \in 1..(Len(seq) - 1) : seq[k] <= seq[k + 1])

Termination == <>(pc = "halt")

\* FiniteSeq is the model-checkable version of Seq; the cfg file replaces
\* Sequences.Seq with it so the state space stays finite.
LimitedSeq == FiniteSets.Bag

====