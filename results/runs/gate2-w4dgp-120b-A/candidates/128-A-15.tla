---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

Domain == 1..MaxSeqLen
Intervals == {i \in Domain : i \in Domain} \X {j \in Domain : j \in Domain}

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

PartialSort == [i \in Domain, j \in Domain |-> IF i <= j THEN 1 ELSE 0]

\* A permutation of a sequence is the result of composing it with an automorphism of the domain.
Perm(s) == {s \circ f : f \in [Domain -> Domain] : \A x \in Domain : \E y \in Domain : f[x] = y}
AutoPerm(s) == {f \in [Domain -> Domain] : \A x, y \in Domain : (f[x] = f[y]) => (x = y)}
Permutes(x) == \E y \in Perm(x) : y = seq
Sorted(s) == \A i, j \in DOMAIN s : (i <= j) => (s[i] <= s[j])

\* The partition operator abstracts away the whole partition procedure.  It accepts any
\* sequence that is a valid result of partitioning the given interval around the given pivot.
Partitioned(s, lo, hi, p) == (s = seq)
    /\ (p \in lo..hi)
    /\ (\A i \in Domain : (i < lo \/ i > hi) => s[i] = seq[i])
    /\ (\A i \in lo..p : \A j \in p+1..hi : s[i] <= s[j])
    /\ (\A y \in DOMAIN s : \E x \in DOMAIN s : s[y] = seq[x])

TypeOK ==
    /\ seq \in [Domain -> Values]
    /\ orig \in [Domain -> Values]
    /\ work \subseteq Domain \X Domain
    /\ pc \in {"loop", "done"}

Init ==
    /\ seq \in [Domain -> Values]
    /\ seq # [i \in Domain |-> CHOOSE v \in Values : TRUE]
    /\ orig = seq
    /\ work = {<<1, MaxSeqLen>>}
    /\ pc = "loop"

\* One Quicksort step: pick an interval, partition it, and replace it with its subintervals.
Loop ==
    /\ pc = "loop"
    /\ \E I \in work :
        /\ work' = (work \ {I}) \cup (IF I[1] = I[2] THEN {} ELSE
                {<<I[1], I[2]>>} \cup {<<I[1], I[2]>>})
        /\ \E s \in [Domain -> Values] : /\ Partitioned(s, I[1], I[2], I[2])
                                         /\ seq' = s
        /\ IF I[1] = I[2] THEN UNCHANGED seq ELSE UNCHANGED seq
    /\ pc' = pc
    \/ /\ pc = "loop"
       /\ work = {}
       /\ pc' = "done"
       /\ UNCHANGED <<seq, orig, work>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Loop \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

\* Termination plus partial correctness: the final sequence is a sorted permutation of the
\* input if the algorithm ever terminates.
PCorrect == (pc = "done") => (\A x \in Permutes(orig) : x = seq /\ Sorted(seq))
Termination == <>(pc = "done")

\* The invariant used for the structured proof: everything the algorithm knows stays true.
Inv == /\ work \subseteq Domain \X Domain
       /\ (\A lo, hi \in Domain : <<lo, hi>> \in work => lo <= hi)
       /\ Permutes(orig)
       /\ (\A lo, hi \in Domain : (<<lo, hi>> \in work /\ lo < hi) => PartialSort[seq, lo, hi] = 0)

PCorrectInv == (pc = "done") => (\A x \in Permutes(orig) : x = seq /\ Sorted(seq))

====