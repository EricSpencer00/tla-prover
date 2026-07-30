---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

WorkSpace == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

TypeOK ==
    /\ seq \in Seq
    /\ orig \in Seq
    /\ todo \subseteq WorkSpace
    /\ pc \in {"loop", "done"}

\* An interval contains a single element (a sorted unit).
SingletonInterval(w) == w.lo = w.hi

\* The partition operator: any sequence that leaves the outside unchanged,
\* and moves everything at or below the pivot index to positions at or below
\* the pivot, while moving everything above it to positions above.
Partitions(w, p) ==
    { s \in Seq :
        /\ \A i \in 1..Len(s) : (i < w.lo \/ i > w.hi) => s[i] = seq[i]
        /\ \A i \in w.lo..p : \A j \in p+1..w.hi => s[i] <= s[j] }

Update(seq, w, p) == CHOOSE s \in Partitions(w, p) : TRUE

DomainPartitions ==
    /\ \A w1 \in todo, w2 \in todo : w1 # w2 => w1.hi < w2.lo \/ w2.hi < w1.lo
    /\ \A w \in todo : w.hi <= Len(seq)

Permutation == \E f \in [1..Len(seq) -> 1..Len(seq)] :
    \A g \in [1..Len(seq) -> 1..Len(seq)] :
        (g \in [1..Len(seq) -> 1..Len(seq)] /\ \A y \in 1..Len(seq) : f[g[y]] = y)
          => seq = orig

RelativelySorted ==
    \A w1 \in todo, w2 \in todo :
        (w1.hi < w2.lo) => (seq[w1.hi] <= seq[w2.lo])

Inv == DomainPartitions /\ Permutation /\ RelativelySorted

Init ==
    /\ seq = Seq
    /\ orig = Seq
    /\ todo = {[lo |-> 1, hi |-> Len(Seq)]}
    /\ pc = "loop"

Step ==
    /\ pc = "loop"
    /\ \E w \in todo :
        /\ LET gone == todo \ {w} IN
           /\ IF SingletonInterval(w)
                THEN /\ todo' = gone
                ELSE /\ \E p \in w.lo..w.hi :
                        /\ seq' = Update(seq, w, p)
                        /\ todo' = gone \cup {[lo |-> w.lo, hi |-> p], [lo |-> p+1, hi |-> w.hi]}
           /\ UNCHANGED orig
    /\ UNCHANGED pc

Done ==
    /\ pc = "loop"
    /\ todo = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, orig, todo>>

Quiesce == (pc = "done") /\ UNCHANGED vars

Next == Step \/ Done \/ Quiesce

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Step)

\* Partial correctness: every terminated run is a sorted permutation of the input.
PCorrect ==
    (pc = "done") => (seq = orig /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i+1])

\* Weak fairness on the step relation drives eventual termination.
Termination ==
    (pc = "loop") ~> (pc = "done")

====