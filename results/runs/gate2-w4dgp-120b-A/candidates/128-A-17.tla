---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* A bounded-length, value-limited version of the standard Seq operator; this
\* is the name the .cfg replaces, so it must be defined here and must not be
\* listed as a declared constant itself.
LimitedSeq(f) == CHOOSE s \in {g \in Seq(Vals) : Len(g) <= MaxSeqLen} : f = s

\* Permutations are captured as compositions with automorphisms of the index domain.
Automorphisms(d) == {f \in [d -> d] : \A a, b \in d : f[a] = f[b] => a = b}
Permutations(x) == {y \in Seq(Vals) : \E f \in Automorphisms(Domain(x)) : y = [i \in Domain(x) |-> x[f[i]]]}

\* The partition primitive: for a given interval and pivot, every sequence that leaves
\* outside the interval untouched and respects the pivot ordering is possible.
Partition(seq, intv, p) ==
  {s \in Permutations(seq) :
     \A i \in Domain(s) :
       ((i \in intv) /\ (i <= p)) => s[i] <= s[p]
       /\ ((i \in intv) /\ (i > p)) => s[i] >= s[p]
       /\ (i \notin intv) => s[i] = seq[i]}

Intervals == {intv \in DOMAIN(Domain({1 : 0})) : intv # {}}
IntervalsSubset == {intv \in Intervals : intv # {}}

VARIABLES seq, origSeq, workSet, pc

vars == <<seq, origSeq, workSet, pc>>

TypeOK ==
  /\ seq \in Seq(Vals)
  /\ origSeq \in Seq(Vals)
  /\ workSet \subseteq Intervals
  /\ pc \in {"main"}

Init ==
  /\ \E s \in {g \in Seq(Vals) : Len(g) >= 1 /\ Len(g) <= MaxSeqLen} : seq = s /\ origSeq = s
  /\ workSet = {{1 .. Len(seq)}}
  /\ pc = "main"

Range(i) == {j \in INTEGER : i[1] <= j /\ j <= i[2]}

\* The algorithm's one atomic step: pick an interval, and either discard it if
\* it is a singleton or partition it and subdivide it.
OneStep ==
  /\ pc = "main"
  /\ workSet # {}
  /\ \E intv \in workSet :
       /\ workSet' = workSet \ {intv}
       /\ IF Cardinality(intv) = 1 THEN UNCHANGED seq
          ELSE
            \E p \in Range(intv) :
              /\ LET lower == {j \in intv : j <= p}
                     upper == {j \in intv : j > p}
                     newseq \in Partition(seq, intv, p)
                     nset == IF lower = {} THEN {} ELSE {lower}
                     uset == IF upper = {} THEN {} ELSE {upper}
                     newSet == nset \cup uset
              IN /\ seq' = newseq
                 /\ workSet' = workSet \cup newSet
  /\ UNCHANGED <<origSeq, pc>>

Terminate ==
  /\ pc = "main"
  /\ workSet = {}
  /\ pc' = "main"
  /\ UNCHANGED <<seq, origSeq, workSet>>

Next ==
  \/ OneStep
  \/ Terminate
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(OneStep) /\ WF_vars(Terminate)

\* A pair of intervals that are both active but whose index ranges are disjoint.
Disjoint(i, j) == i # {} /\ j # {} /\ Cardinality(i) > 1 /\ Cardinality(j) > 1 /\ i \cap j = {}

PCorrect == workSet = {} => (seq \in Permutations(origSeq) /\ \A i, j \in Domain(seq) : (i <= j) => seq[i] <= seq[j])

\* The inductive invariant: (1) intervals are always genuine subsets of the index
\* domain, (2) the current sequence is always a permutation of the original, and
\* (3) any two active, disjoint intervals are already relatively sorted.
Inv ==
  /\ workSet \subseteq IntervalsSubset
  /\ seq \in Permutations(origSeq)
  /\ \A i, j \in Domain(seq) : Disjoint(i, j) => \A k \in i, l \in j : k <= l => seq[k] <= seq[l]

Termination == <>(pc = "main" /\ workSet = {})

====