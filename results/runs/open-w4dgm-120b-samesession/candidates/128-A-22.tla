---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Permutations

\* Quicksort modeled as a single-loop state machine, with the partition step
\* abstracted to "choose any valid partition result" rather than simulated.
CONSTANTS Values, MaxSeqLen

Intervals == {r \in SUBSET (1..MaxSeqLen) : r # {} /\ \E a, b \in r : \A c \in r : a <= c /\ c <= b}

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ orig \in Seq(Values)
  /\ Len(orig) <= MaxSeqLen
  /\ todo \subseteq Intervals
  /\ pc \in {"loop", "done"}

\* A partition of s on interval r around pivot i keeps everything outside r fixed
\* and forces the pivot property. It is the complete nondeterministic choice set
\* for the partition step -- not a deterministic scheme.
Partitions(s, r, i) ==
  {t \in Seq(Values) :
     /\ Len(t) = Len(s)
     /\ \A c \in 1..Len(s) : IF c \in r THEN t[c] \in Values ELSE t[c] = s[c]
     /\ \A a \in 1..i : \A b \in (i+1)..Len(s) : a \in r /\ b \in r => t[a] <= t[b]}

Init ==
  /\ \E s \in Seq(Values) : (Len(s) >= 1 /\ Len(s) <= MaxSeqLen /\ seq = s /\ orig = s)
  /\ todo = {[1..Len(seq]]}
  /\ pc = "loop"

Loop ==
  \/ pc = "loop" /\ todo # {}
     /\ \E r \in todo :
          /\ \E i \in r :
               /\ \E t \in Partitions(seq, r, i) :
                    /\ seq' = t
                    /\ todo' = (todo \ {r}) \cup {[1..i], (i+1)..Len(t]}
          /\ UNCHANGED orig
  \/ pc' = "done"

Stall == pc = "done" /\ UNCHANGED vars

Next == Loop \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

Sorted(s) == \A a, b \in 1..Len(s) : a <= b => s[a] <= s[b]

PCorrect ==
  /\ (pc = "done" => (Sorted(seq) /\ seq \in Permutations(orig)))
  /\ Len(seq) <= MaxSeqLen
  /\ \A a, b \in todo : a # b => (a \cap b = {} \/ a = b)

TypeOKOK == TypeOK

\* The partition relation on one interval must preserve the domain partitioning:
\* the intervals in the todo set stay pairwise disjoint and their union is not
\* shrunk as the algorithm proceeds, which is what makes the per-interval sortedness
\* a global sortedness property once every interval has collapsed.
Inv ==
  /\ todo # {}
  /\ \A a, b \in todo : a # b => (a \cap b = {})
  /\ \A a \in todo : a \subseteq 1..Len(seq)
  /\ \A a \in todo : \A x, y \in a : (x < y) => seq[x] <= seq[y]

Termination == <>(pc = "done")
====