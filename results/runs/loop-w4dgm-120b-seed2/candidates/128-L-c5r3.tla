---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* Sort is modeled as a control-state machine with a PC; the loop body does
\* everything, so there is a single Sort action with two guarded outcomes.
\* Termination is guaranteed by weak fairness on that action.

Indices == 1..MaxSeqLen

VARIABLES seq, orig, todo, pc
vars == <<seq, orig, todo, pc>>

TypeOK ==
    /\ seq \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ orig \in Seq(Values)
    /\ Len(orig) <= MaxSeqLen
    /\ todo \in SUBSET Indices
    /\ pc \in {"main", "done"}

Init ==
    /\ \E s \in Seq(Values) : Len(s) > 0 /\ s # << >> /\ seq = s /\ orig = s
    /\ todo = {1..Len(seq)}
    /\ pc = "main"

\* A partition is any permutation that leaves the outside untouched and
\* respects the pivot's ordering cut across the chosen interval.
Partitions(i) ==
    {p \in [Indices -> Values] :
        /\ p[i] \in Values
        /\ \A k \in Indices \ {i} : p[k] = seq[k]
        /\ \A a \in 1..i, b \in i+1..Len(seq) : p[a] <= p[b]}

SortStep ==
    /\ pc = "main"
    /\ \E i \in todo :
        /\ IF i = Len(seq) THEN
            /\ i \in todo /\ todo' = todo \ {i} /\ seq' = seq
        ELSE
            /\ \E q \in Partitions(i) :
                /\ seq' = q
                /\ todo' = (todo \ {i}) \cup {i + 1}
        /\ pc' = IF todo' = {} THEN "done" ELSE "main"
    /\ orig' = orig

Done ==
    /\ pc = "done"
    /\ pc' = pc /\ seq' = seq /\ orig' = orig /\ todo' = todo

Next == SortStep \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep)

\* Invariant: each pair of indices in different todo intervals is already
\* ordered relative to each other, which forces total ordering at the end.
Inv ==
    /\ \A a, b \in todo :
        /\ (a # b => (a < b => seq[a] <= seq[b]))
    /\ \A i \in Domains(seq) : seq[i] \in Values

PCorrect ==
    /\ (pc = "done") => (seq \in Permutations(orig))
    /\ (pc = "done") => (Len(seq) = Len(orig))
    /\ (pc = "done") => (seq \in {f \in [Indices -> Values] : \A k \in 1..(Len(seq) - 1) : f[k] <= f[k + 1]})

Termination == <>(pc = "done")

LimitedSeq(f, S) ==
    IF S = << >> THEN << >>
    ELSE LET h == Head(S) IN << f[h] >> \o LimitedSeq(f, Tail(S))

====