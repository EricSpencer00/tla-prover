---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The standard Sequences module defines Seq as an unrestricted infinite
\* operator. For model checking we need a bounded, finite version, so the
\* .cfg file replaces Seq with LimitedSeq. Keep EXTENDS Sequences, but do
\* not declare or redefine Seq itself; the replacement is injected by TLC.
LimitedSeq(n, S) == CHOOSE f \in [1..n -> S] : \A k \in 1..n : f[k] = CHOOSE x \in S : TRUE

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

TypeOK ==
  /\ seq \in [0..MaxSeqLen -> Values \cup {"none"}]
  /\ original \in [0..MaxSeqLen -> Values \cup {"none"}]
  /\ work \subseteq (0..MaxSeqLen \X 0..MaxSeqLen)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E n \in 1..MaxSeqLen, s \in [1..n -> Values] :
       /\ seq = [k \in 0..MaxSeqLen |-> IF k \in 1..n THEN s[k] ELSE "none"]
       /\ original = [k \in 0..MaxSeqLen |-> IF k \in 1..n THEN s[k] ELSE "none"]
  /\ work = {<<1, MaxSeqLen>>}
  /\ pc = "loop"

\* A valid partition leaves elements outside the interval intact and arranges
\* those at or below the pivot index to be no greater than those above it.
ValidPartitions(I, p) ==
  {s \in [0..MaxSeqLen -> Values \cup {"none"}] :
     /\ \A k \in 0..MaxSeqLen : (k < I[1] \/ k > I[2]) => s[k] = seq[k]
     /\ \A k \in I[1]..I[2], m \in I[1]..I[2] :
          (k <= p /\ m > p) => s[k] <= s[m]}

Iterate ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E I \in work :
       /\ work' = work \ {I}
       /\ IF I[1] = I[2]
          THEN work' = work' \cup {I}
          ELSE \E p \in I[1]..I[2] :
                 /\ work' = work' \cup {<<I[1], p>>} \cup {<<p+1, I[2]>>}
                 /\ \E s \in ValidPartitions(I, p) : seq' = s
  /\ pc' = pc

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, work>>

Stall == UNCHANGED vars

Next == Iterate \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Iterate) /\ WF_vars(Terminate)

DomainPartitions ==
  /\ work # {}
  /\ \A i \in 1..MaxSeqLen : \E I \in work : i \in I[1]..I[2]

PermutationsPreserved ==
  \A k \in 0..MaxSeqLen :
    /\ original[k] = "none" => seq[k] = "none"
    /\ original[k] # "none" => \E i \in 1..MaxSeqLen : original[i] = seq[k]

RelativeSortedness ==
  \A i, j \in 0..MaxSeqLen :
    /\ seq[i] # "none" /\ seq[j] # "none"
    /\ (\E I \in work : i \in I[1]..I[2] /\ j \in I[1]..I[2] /\ i < j) => seq[i] <= seq[j]

Inv == DomainPartitions /\ PermutationsPreserved /\ RelativeSortedness

PCorrect ==
  (pc = "done") => (PermutationsPreserved /\ RelativeSortedness)

Termination == <>(pc = "done")

====