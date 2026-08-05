---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Automorphisms

CONSTANTS Values, MaxSeqLen

\* LimitedSeq is a checkable variant of the infinite Seq operator from Sequences;
\* it keeps the same semantics but only for sequences up to MaxSeqLen.
Seq(s) == { t \in (1..MaxSeqLen -> Values) : \A i \in 1..MaxSeqLen : i <= Len(s) => t[i] = s[i] }

\* A partition of s over interval i..j around pivot p leaves everything outside i..j unchanged and
\* places everything at or below the pivot no greater than everything above it.
Partitions(s, i, j, p) ==
  { t \in Seq(s) :
      /\ \A k \in 1..Len(s) : (k < i \/ k > j) => t[k] = s[k]
      /\ \A k \in i..p, l \in p+1..j : t[k] <= t[l]
      /\ \A k \in i..p : t[k] \in { s[z] : z \in i..j }
      /\ \A k \in p+1..j : t[k] \in { s[z] : z \in i..j }
  }

VARIABLES seq, origSeq, todo, pc
vars == <<seq, origSeq, todo, pc>>

TypeOK ==
  /\ seq \in Seq([1..MaxSeqLen -> Values])
  /\ origSeq \in Seq([1..MaxSeqLen -> Values])
  /\ todo \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
  /\ pc \in { "main", "done" }

Init ==
  /\ seq \in Seq([1..MaxSeqLen -> Values]) /\ Len(seq) > 0
  /\ origSeq = seq
  /\ todo = { <<1, Len(seq)>> }
  /\ pc = "main"

\* The sorting loop: repeatedly take an interval out of the work set and partition it.
Step(i, j) ==
  /\ pc = "main"
  /\ <<i, j>> \in todo
  /\ LET Sub == { <<i, p>>, <<p+1, j>> : p \in i..j-1 } IN
     \/ /\ i = j
        /\ todo' = todo \ {<<i, j>>}
        /\ UNCHANGED <<seq, origSeq>>
     \/ /\ i < j
        /\ \E p \in i..j-1, t \in Partitions(seq, i, j, p) :
             /\ seq' = t
             /\ todo' = (todo \ {<<i, j>>}) \cup Sub
        /\ UNCHANGED <<origSeq>>
     /\ pc' = "main"
  \/ (pc = "main" /\ todo = {} /\ pc' = "done" /\ UNCHANGED <<seq, origSeq, todo>>)
  \/ (pc = "done" /\ UNCHANGED vars)

Next == \E i, j \in 1..MaxSeqLen : Step(i, j)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The algorithm is partially correct: termination means the final sequence is a sorted
\* permutation of the original.
Permutation(s, t) == \E f \in Automorphisms(Domain(s)) : \A i \in Domain(s) : t[i] = s[f[i]]

PCorrect ==
  pc = "done" =>
    /\ Permutation(origSeq, seq)
    /\ \A i, j \in 1..MaxSeqLen : i < j => seq[i] <= seq[j]

Inv ==
  /\ \A i, j \in 1..MaxSeqLen : <<i, j>> \in todo => i <= j
  /\ Permutation(origSeq, seq)
  /\ \A i, j, k, l \in 1..MaxSeqLen : (i <= j /\ <<k, l>> \in todo) => (j < k \/ j >= l \/ seq[i] <= seq[j])

Termination == (pc = "done") ~> (pc = "done")
====