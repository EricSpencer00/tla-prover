---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

ASSUME Values \subseteq Int /\ Cardinality(Values) \in Nat /\ MaxSeqLen \in Nat

RECURSIVE PermOf(_, _)
PermOf(k, s) ==
    IF k = 0 THEN {}
    ELSE { [[i |-> s[i], j |-> s[k]] : s \in [1..k -> Values]]
               \cup PermOf(k - 1, s)}

RECURSIVE IsPermutation(_, _)
IsPermutation(p, q) ==
    IF Len(p) = 0 THEN Len(q) = 0
    ELSE \E j \in 1..Len(q) : p[1] = q[j] /\ IsPermutation(SubSeq(p, 2, Len(p)), DeleteSeq(q, j))

RECURSIVE Sorted(_)
Sorted(s) ==
    IF Len(s) <= 1 THEN TRUE
    ELSE s[1] <= s[2] /\ Sorted(SubSeq(s, 2, Len(s)))

Intervals == UNION { [a .. b] : a, b \in 1..MaxSeqLen, a <= b }

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Init ==
    /\ seq \in PermOf(MaxSeqLen, Values)
    /\ Len(seq) >= 1
    /\ orig = seq
    /\ work = {[1, Len(seq)]}
    /\ pc = "loop"

\* The partition step is abstracted: any valid partition outcome is chosen at once.
Step ==
    \/ \E rng \in work :
         /\ Cardinality(rng) = 1
         /\ work' = work \ {rng}
         /\ UNCHANGED <<seq, orig>>
    \/ \E rng \in work, p \in rng[1] .. rng[2] :
         /\ Cardinality(rng) > 1
         /\ \E ns \in PermOf(MaxSeqLen, Values) :
              /\ IsPermutation(ns, seq)
              /\ \A i \in 1..MaxSeqLen :
                   (i < rng[1] \/ i > rng[2]) => ns[i] = seq[i]
              /\ \A i \in rng[1] .. p : \A j \in p + 1 .. rng[2] : ns[i] <= ns[j]
              /\ seq' = ns
         /\ work' = (work \ {rng}) \cup {[rng[1], p], [p + 1, rng[2]]}
         /\ UNCHANGED orig
    /\ pc' = "loop"
    \/ ~(work = {}) /\ pc' = "done" /\ UNCHANGED <<seq, orig, work>>

Next == Step \/ (pc = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

TypeOK ==
    /\ seq \in PermOf(MaxSeqLen, Values)
    /\ orig \in PermOf(MaxSeqLen, Values)
    /\ work \subseteq Intervals
    /\ pc \in {"loop", "done"}

\* The invariant combines permutation, sortedness, and boundary consistency.
Inv ==
    /\ pc = "done" => IsPermutation(seq, orig)
    /\ pc = "done" => Sorted(seq)
    /\ Cardinality(work) = 0 => pc = "done"
    /\ \A rng \in work : rng[1] >= 1 /\ rng[2] <= Len(seq)

PCorrect == pc = "done" => Sorted(seq)

Termination == <>(pc = "done")

====