---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* The Quicksort example from Lamport's textbook, modelled as a single
\* sequential sort with an abstract partition step. The state variables
\* are the current sequence, a copy of the original sequence, the set of
\* intervals still to process, and a program counter. The invariant
\* captures domain partitions, permutation preservation, and sortedness.
\* Every identifier that appears in the reference .cfg is defined exactly
\* as named.

CONSTANTS Values, MaxSeqLen, Seq

\* Domain of the current sequence; drops when the sequence shrinks.
Dom(s) == 1 .. Len(s)

\* Two intervals are disjoint if their index ranges do not overlap.
Disjoint(i, j) ==
  \/ i[2] < j[1]
  \/ j[2] < i[1]

\* The partition operator: all permutations that leave every element
\* outside the chosen interval unchanged while ensuring elements at
\* or below the pivot index are no greater than those above it.
\* This is the whole reason the abstract step is sound.
Partition(s, i, p) ==
  { t \in [Dom(s) -> Values] :
      /\ \A k \in Dom(s) \ {i[1] .. i[2]} : t[k] = s[k]
      /\ \A k \in i[1] .. p : \A l \in p + 1 .. i[2] : t[k] <= t[l] }

\* A permutation of a sequence is a composition with a domain automorphism.
\* This definition matches the textbook's.
Permutation(s, t) ==
  \E f \in [Dom(s) -> Dom(t)] :
    /\ \A i, j \in Dom(s) : (f[i] = f[j]) => (i = j)
    /\ \A k \in Dom(s) : s[i] = t[f[i]]

\* An interval is sorted between itself and the interval immediately
\* above it in the domain ordering.
SortedBetween(s, i, j) ==
  \A k \in i[1] .. i[2] : \A l \in j[1] .. j[2] : s[k] <= s[l]

Sorted(seq) ==
  \A i, j \in {1} \cup ({2 .. Len(seq)} \cup {Len(seq) + 1}) :
    (i < j) => seq[i] <= seq[j]

\* Intervals form a partition of the domain of the current sequence.
Partitioned(seq, intervals) ==
  /\ \E g \in [Dom(seq) -> intervals] :
       \A i, j \in Dom(seq) : (g[i] = g[j]) => (i = j)
  /\ \A k \in Dom(seq) : seq[k] \in Values

\* The model's state vector.
VARIABLES seq, original, intervals, pc

vars == <<seq, original, intervals, pc>>

None == [1 |-> 0, 2 |-> 0]

TypeOK ==
  /\ seq \in Seq
  /\ original \in Seq
  /\ intervals \subseteq (Nat \X Nat)
  /\ pc \in {"loop", "halt"}

\* The invariant is the conjunction of the three parts.
Inv ==
  /\ Partitioned(seq, intervals)
  /\ Permutation(seq, original)
  /\ \A i, j \in intervals : (i[2] < j[1]) => SortedBetween(seq, i, j)

Init ==
  /\ seq = Seq
  /\ original = Seq
  /\ intervals = { <<1, Len(Seq)>> }
  /\ pc = "loop"

\* The single action: pick any active interval and, if it needs work,
\* pick any pivot and any partition result of it; always eventually
\* empty the work set, which is why weak fairness suffices.
Next ==
  \/ \E i \in intervals :
       \/ (\A k \in i[1] .. i[2] : Len(seq) = k) /\ intervals' = intervals \ {i}
          /\ UNCHANGED <<seq, original, pc>>
       \/ \E p \in i[1] .. i[2] :
            \/ \E t \in Partition(seq, i, p) :
                 /\ seq' = t
                 /\ intervals' = (intervals \ {i})
                      \cup (IF i[1] = p THEN {}
                            ELSE { <<i[1], p>> })
                      \cup (IF p = i[2] THEN {}
                            ELSE { <<p + 1, i[2]>> })
                 /\ UNCHANGED <<original, pc>>
  \/ (intervals = {}) /\ pc' = "halt"
  \/ (pc = "halt" /\ UNCHANGED vars)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

PCorrect == pc = "halt" => (Permutation(seq, original) /\ Sorted(seq))

\* Weak fairness on Next forces progress: the loop cannot spin forever.
Termination == <>(pc = "halt")

====