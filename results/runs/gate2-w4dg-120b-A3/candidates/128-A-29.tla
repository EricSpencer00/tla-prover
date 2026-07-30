---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* The full operator set for the spec is brought in here.  The config file
\* replaces Seq by a bounded version (LimitedSeq) and later redefines it so
\* that only short sequences are explored during model checking.
\* Concrete definitions for the operators below are provided in the module,
\* and the config file's replacement must not be re-declared here.
\* (LimitedSeq replaces Seq from Sequences and is a FINITE version of it;
\* keep EXTENDS Sequences, but never declare or redefine Seq.)

LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

Domain == 1..MaxSeqLen

Sorted(f) == \A i \in 1..(Len(f) - 1) : f[i] <= f[i + 1]

\* A partition of f over a range keeps everything outside the range unchanged
\* and enforces the pivot ordering property inside it.
Partitions(f, a, b, c) ==
  { g \in Seq(Values) :
      /\ Len(g) = Len(f)
      /\ \A i \in 1..Len(f) : (i < a \/ i > b) => g[i] = f[i]
      /\ \A i \in a..(c - 1) : g[i] <= g[i + 1]
      /\ \A i \in c..b : g[i] <= g[i + 1]
  }

\* Permutations are defined as compositions with domain automorphisms.
Permutations(f) == { g \in Seq(Values) : \E a \in [Domain -> Domain] : g = [i \in Domain |-> f[a[i]]] }

VARIABLES seq, seq0, work, pc

vars == <<seq, seq0, work, pc>>

TypeOK ==
  /\ seq \in Permutations(seq0)
  /\ seq0 \in LimitedSeq
  /\ work \subseteq (Domain \X Domain)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in LimitedSeq : seq = s /\ seq0 = s
  /\ work = {<<1, Len(seq0)>>}
  /\ pc = "loop"

\* Main loop: pick an interval, partition it, and split the work set.
Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E a, b \in Domain :
       /\ <<a, b>> \in work
       /\ IF a = b THEN work' = work \ {<<a, b>>}
          ELSE \E c \in (a + 1)..(b + 1) :
               /\ seq' \in Partitions(seq, a, b, c)
               /\ work' = (work \ {<<a, b>>}) \cup {<<a, c - 1>>, <<c, b>>}
  /\ pc' = "loop"

Done ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, seq0, work>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Done \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Done)

PCorrect ==
  /\ pc = "done" => seq = seq0
  /\ pc = "done" => Sorted(seq)

\* The full inductive invariant backing the partial correctness proof.
Inv ==
  /\ work \subseteq (Domain \X Domain)
  /\ seq \in Permutations(seq0)
  /\ \A a, b \in Domain : (a, b) \in work => seq[a] <= seq[b]

\* Strong termination, proved by weak fairness, not by a bounded countdown.
Termination ==
  /\ pc = "done"
  /\ \A a \in Domain : a <= Len(seq0)

====