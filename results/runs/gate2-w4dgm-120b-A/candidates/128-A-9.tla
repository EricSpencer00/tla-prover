---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* Quicksort partitioning is abstracted as a nondeterministic choice of any
\* resulting sequence that respects the partition condition, which is what
\* keeps the model finite-state and independent of a concrete partition routine.

VARIABLES seq, orig, todo, pc
vars == <<seq, orig, todo, pc>>

\* A permutation is a bijection on domain positions; two such bijections can
\* be composed pointwise.  Permutations are functions with finite domain, so they
\* are not ZF bijections but that is sufficient for this finite model.
Permutation == [1..MaxSeqLen -> 1..MaxSeqLen]
Compose(p, q) == [i \in DOMAIN p |-> q[p[i]]]

PermutationOf(s) == { Compose(p, q) : p \in Permutations(DOMAIN s), q \in Permutations(DOMAIN s) }

\* The partition operator: keep everything outside the interval untouched and
\* require the left side's values to be no greater than every right side value.
Split(s, a, b, k) ==
  { t \in PermutationOf(s) :
      \A i \in DOMAIN s :
        (i < a \/ i > b) => t[i] = s[i]
      /\ \A i \in a..k, j \in (k+1)..b : s[i] <= s[j] }

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ todo \subseteq (1..MaxSeqLen \X 1..MaxSeqLen)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in (Seq(Values) \ {<<>>}) : seq = s /\ orig = s
  /\ todo = {<<1, Len(seq)>>}
  /\ pc = "loop"

\* When the work set is empty the procedure terminates; this is not a deadlock
\* because the terminating state has a self-loop (the Stutter action).
Next ==
  \/ \E a, b \in 1..MaxSeqLen :
       /\ <<a, b>> \in todo
       /\ todo' = todo \ {<<a, b>>}
       /\ IF a = b
          THEN UNCHANGED <<seq, orig, pc>>
          ELSE \E k \in a..b, s \in Split(seq, a, b, k) :
                 seq' = s
                 /\ todo' = todo \cup {<<a, k>>, <<k+1, b>>}
       /\ pc' = IF <<a, b>> \in todo THEN "loop" ELSE "done"
  \/ (pc = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Sorted(s) == \A i \in DOMAIN s : \A j \in DOMAIN s : i <= j => s[i] <= s[j]

\* The invariant is stronger than the theorem's partial correctness: it is
\* preserved through every iteration, not only at termination.
Inv ==
  /\ \A a, b \in 1..MaxSeqLen : (a, b \in todo) => a <= b
  /\ seq \in {orig[i] : i \in DOMAIN orig}
  /\ \A a, b \in 1..MaxSeqLen : (a, b \in todo) => \A i, j \in a..b : i <= j => seq[i] <= seq[j]

PCorrect == (pc = "done") => (Sorted(seq) /\ seq \in {orig[i] : i \in DOMAIN orig})

Termination == (pc # "loop") ~> (pc = "done")

Stutter == (pc = "done") /\ UNCHANGED vars

====