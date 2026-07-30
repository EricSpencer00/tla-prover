---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* This TLA+ module is the PlusCal-to-TLA translation of an abstract
\* Quicksort implementation (the one described in the exercise prompt),
\* plus a small hand-written invariant suite and a liveness property
\* saying that the algorithm always reaches its terminal label.  The
\* model checker will use the constant Values as a bounded value set and
\* the constant Seq as the (finite) set of input sequences to explore.

CONSTANTS Values, MaxSeqLen, Seq

SeqLen == Len(Seq)

\* The work set is a set of intervals of the current sequence.  Every
\* interval's indices are in range and the intervals partition the
\* domain.
Interval == [low: 1..SeqLen, high: 1..SeqLen]

DomainOK(S) == /\ \A i \in DOMAIN S : S[i] \in Values
              /\ SeqLen \in DOMAIN S

Subdomains(S, S1, S2) == /\ DOMAIN S1 \cup DOMAIN S2 = DOMAIN S
                         /\ DOMAIN S1 \cap DOMAIN S2 = {}
                         /\ \A a \in DOMAIN S1, b \in DOMAIN S2 : a < b

\* A permutation of a sequence on the domain 1..n is expressed by an
\* automorphism of that domain -- a 1-1, onto map on the indices.
Permutation(n) == {f \in [1..n -> 1..n] : Cardinality(rng f) = n}

Permutes(S, T) == \E f \in Permutation(Domain(S)) : T = [i \in Domain(S) |-> S[f[i]]]

\* The partition operator used by the algorithm: for a chosen interval
\* and pivot index, all elements at or below the pivot are no greater
\* than all elements above it, and every other element is unchanged.
Partition(S, intr, p) == {T \in Permutation(Domain(S)) :
                            /\ \A i \in 1..SeqLen : i \notin intr.low..intr.high => T[i] = S[i]
                            /\ \A i, j \in intr.low..intr.high :
                                 (i <= p /\ p < j) => T[i] <= T[j]}

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

TypeOK ==
  /\ seq \in [1..SeqLen -> Values]
  /\ original \in [1..SeqLen -> Values]
  /\ work \subseteq Interval
  /\ pc \in {"L1", "Term"}

Init ==
  /\ seq = Seq
  /\ original = Seq
  /\ work = {[low |-> 1, high |-> SeqLen]}
  /\ pc = "L1"

BothEmpty == (work = {}) /\ (pc = "Term")

\* The algorithm is a single while loop over the work set.  When an
\* interval has more than one element, partitioning picks an arbitrary
\* valid post-partition sequence; when it has one element it simply
\* drops the interval from the work set.
Step ==
  /\ pc = "L1"
  /\ \E intr \in work :
       /\ work' = work \ {intr}
       /\ IF intr.low = intr.high
          THEN UNCHANGED seq
          ELSE
            /\ \E p \in intr.low..intr.high :
                 /\ \E T \in Partition(seq, intr, p) : seq' = T
            /\ work' = work' \cup {[low |-> intr.low, high |-> p]}
                 \cup {[low |-> p + 1, high |-> intr.high]}
  /\ pc' = IF work = {} THEN "Term" ELSE "L1"

Stall == UNCHANGED vars

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Termination of the sort.
Termination == <>(pc = "Term")

\* The partial correctness condition: a terminated run has produced a
\* sorted permutation of the original input.
PCorrect ==
  /\ pc = "Term"
  /\ Permutes(original, seq)
  /\ \A i \in 1..SeqLen - 1 : seq[i] <= seq[i + 1]

\* The full invariant suite: an inductive invariant of domain
\* partitioning plus the two weaker properties of permutation
\* preservation and partial sortedness between intervals.
Inv ==
  /\ \E S \subseteq [1..SeqLen -> Values] :
       /\ DomainOK(S)
       /\ Permutes(original, S)
       /\ Subdomains(S, seq, S)
  /\ Permutes(original, seq)
  /\ \A a, b \in work : a.high < b.low

====