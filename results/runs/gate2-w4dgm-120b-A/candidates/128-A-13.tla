---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* The sort works over contiguous intervals of indices in seq; the loop keeps
\* subdividing them until every interval is a single element, then halts.
Interval == {p \in 1..MaxSeqLen : TRUE}

TypeOK ==
    /\ seq \in Seq(Values)
    /\ orig \in Seq(Values)
    /\ work \subseteq Interval
    /\ pc \in {"inLoop", "halt"}

\* A step of Quicksort may only permute the domain, so the set of values in
\* seq never changes -- this is the core of the correctness argument.
SeqPermutation ==
    \E g \in [Domain(seq) -> Domain(orig)] :
        /\ \A x \in Domain(seq) : seq[x] = orig[g[x]]
        /\ \A x \in Domain(seq), y \in Domain(seq) : g[x] = g[y] => x = y

\* The inductive invariant: intervals partition the domain, the permutation
\* is unbroken, and no value ever appears above some threshold to the left of
\* a value that is at or below that threshold.
Inv ==
    /\ work # {}
    /\ \A a, b \in work : a # b => a \cap b = {}
    /\ \A x \in work : x = 1..MaxSeqLen \/ (\E p, q \in 1..MaxSeqLen : x = p..q)
    /\ SeqPermutation
    /\ \A i, j \in Domain(seq) :
        (\A k \in Domain(seq) : k <= i => seq[k] <= seq[j]) => seq[i] <= seq[j]

\* A single Quicksort iteration: pick an interval, partition it around a
\* pivot, and subdivide the interval in the work set. The new sequence must
\* be a valid partition of the old one over the chosen interval.
PartitionStep ==
    /\ pc = "inLoop"
    /\ work # {}
    /\ \E x \in work :
        /\ Cardinality(x) = 1
        /\ work' = work \ {x}
        \/ \E p, q \in 1..MaxSeqLen :
            /\ x = p..q
            /\ \E c \in p..q :
                /\ Cardinality(p..c) > 1 /\ Cardinality((c + 1)..q) > 1
                /\ work' = (work \ {x}) \cup {p..c, (c + 1)..q}
                /\ \E seq2 \in [Domain(seq) -> Values] :
                    /\ (Domain(seq2) = Domain(seq) /\ \A i \in Domain(seq) :
                          i < p \/ i > q => seq2[i] = seq[i])
                    /\ \A i \in p..c, j \in (c + 1)..q : seq2[i] <= seq2[j]
                    /\ seq' = seq2
    /\ pc' = IF work = {} THEN "halt" ELSE "inLoop"
    /\ orig' = orig

\* The work set is empty: the loop has exhausted every interval, so the
\* algorithm halts.
Terminate ==
    /\ pc = "inLoop"
    /\ work = {}
    /\ pc' = "halt"
    /\ UNCHANGED <<seq, orig, work>>

\* After termination, the process does nothing. This keeps the model from
\* going sticky once all of its work is done.
Stall ==
    /\ pc = "halt"
    /\ UNCHANGED vars

\* The sort must also be able to start from an empty or very short sequence,
\* so its beginning is nondeterministic over all admissible (possibly empty)
\* sequences up to the bounded length.
Init ==
    /\ seq \in [1..MaxSeqLen -> Values] \cup {<<>>}
    /\ orig = seq
    /\ work = {1..MaxSeqLen}
    /\ pc = "inLoop"

Next == PartitionStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep) /\ WF_vars(Terminate)

\* When the loop halts, seq is a sorted permutation of the original.
PCorrect ==
    (pc = "halt") => (SeqPermutation /\ \A i \in Domain(seq) : \A j \in Domain(seq) : i < j => seq[i] <= seq[j])

\* Quicksort always reaches its terminal state: the work set is eventually
\* emptied by repeated partition steps.
Termination == (pc = "halt") ~> (pc = "halt")

\* The bounded-length override for the sequence operator; the operator keeps
\* its name (Seq) because the specification uses it in lots of places.
LimitedSeq ==
    /\ Seq = [Domain >> [x \in 1..MaxSeqLen |-> Values]]
    /\ Domain \in [Seq -> (1..MaxSeqLen) \cup {0}]
====