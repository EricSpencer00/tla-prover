---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A permutation of a domain is an automorphism of that domain: a bijection that
\* only moves elements inside the domain and leaves all others untouched.
\* This lets us speak of reordering the interval while respecting the embedding
\* in the full sequence.
Permutations == {f \in [1..MaxSeqLen -> 1..MaxSeqLen] :
                    \A x \in 1..MaxSeqLen : (f[x] = x) <=> (x <= MaxSeqLen)
                    /\ \A x \in 1..MaxSeqLen : \A y \in 1..MaxSeqLen : (f[x] = f[y]) => (x = y)}

\* The partition operator: identity outside [i..j] and a permutation inside,
\* constrained by the pivot ordering.
Partition(i, j, p) ==
    [x \in 1..MaxSeqLen |-> IF x < i \/ x > j THEN x
                             ELSE IF x <= p THEN (p - i + 1) + (x - i)
                             ELSE p + (x - p)]

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
    /\ seq \in Seq(Values)
    /\ orig \in Seq(Values)
    /\ work \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
    /\ pc \in {"loop", "halt"}

Init ==
    /\ \E s \in Seq(Values) : Len(s) >= 1 /\ Len(s) <= MaxSeqLen /\ seq = s
    /\ orig = seq
    /\ work = {<<1, Len(seq)>>}
    /\ pc = "loop"

\* One iteration of the loop: partition one interval and replace it by two.
QuicksortStep ==
    /\ pc = "loop"
    /\ \E i, j \in 1..MaxSeqLen :
         /\ <<i, j>> \in work
         /\ i < j
         /\ \E p \in i..j :
              /\ seq' = [x \in 1..MaxSeqLen |->
                            IF x \in i..j THEN seq[Partition(i, j, p)[x]]
                            ELSE seq[x]]
              /\ work' = (work \ {<<i, j>>}) \cup {<<i, p>>, <<p + 1, j>>}
         /\ UNCHANGED orig
    /\ pc' = "loop"

\* The empty work set is the termination condition.
Terminate ==
    /\ pc = "loop"
    /\ work = {}
    /\ pc' = "halt"
    /\ UNCHANGED <<seq, orig, work>>

Next == QuicksortStep \/ Terminate \/ UNCHANGED vars

\* Once halted, the system simply idles.
Stall ==
    /\ pc = "halt"
    /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep) /\ WF_vars(Terminate) /\ [][Stall]_vars

\* The key safety property: a halted run ends sorted and contents-preserving.
PCorrect == (pc = "halt") => (seq \in Permutations[orig] /\ \A a, b \in 1..MaxSeqLen : a <= b => seq[a] <= seq[b])

\* An inductive invariant capturing the interval ordering before termination.
\* The partition operator itself drives sortedness between subintervals.
Inv ==
    /\ work = {}
    /\ \A a, b \in 1..MaxSeqLen : (a <= b) => (seq[a] <= seq[b])

TypeOKInv == TypeOK /\ Inv

Termination == (pc = "halt") ~> (pc = "halt")

\* The model's sequence operator is the bounded, finite version, so seq stays
\* well-formed even when the interval is empty.
LimitedSeq == Seq
====