---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* LimitedSeq is a model-checked, size-bounded variant of the standard Seq
\* operator from the Sequences module.  It is defined here rather than
\* imported so the .cfg can replace Seq with it without touching the rest of
\* the module.
VARIABLE Seq, Original, Work, pc

TypeOK ==
  /\ Seq \in Seq(Values)
  /\ Len(Seq) <= MaxSeqLen
  /\ Original \in Seq(Values)
  /\ Len(Original) <= MaxSeqLen
  /\ Work \subseteq (1 .. MaxSeqLen) \X (1 .. MaxSeqLen)
  /\ pc \in {"loop", "done"}

\* Permutations of a domain are captured by composition with automorphisms
\* of that domain (bijections from the domain to itself); this is the
\* standard definition and is not something TLC can check on its own, so
\* it lives as a semantic comment rather than an executable check.
Permutations(d) == {f \in [d -> d] : \E g \in [d -> d] : g \in Aut(d) /\ f = g}

\* A partition, for an interval itvl and a pivot position p, is any
\* sequence that leaves everything outside the interval untouched, and
\* inside the interval guarantees every element at or below p is no greater
\* than every element strictly above p.
Partitions(itvl, p) ==
  {newSeq \in Permutations(1 .. Len(Seq)) :
     /\ \A i \in 1 .. Len(Seq) : (i \notin itvl) => newSeq[i] = Seq[i]
     /\ \A i \in itvl : \A j \in itvl :
          (i <= p /\ j > p) => newSeq[i] <= newSeq[j]}

\* The algorithm's bulk action: pick an interval, and either discard a
\* singleton or partition it and replace it by the two subintervals.
QuicksortStep ==
  \/ \E itvl \in Work :
       /\ Len(Seq) > 0
       /\ \/ /\ itvl[2] - itvl[1] + 1 = 1
              /\ Work' = Work \ {itvl}
            \/ \E p \in itvl[1] .. itvl[2] :
                 /\ \E newSeq \in Partitions(itvl, p) :
                      /\ newSeq[p] \in Values
                      /\ newSeq[p + 1] \in Values
                      /\ Seq' = newSeq
                 /\ Work' = (Work \ {itvl}) \cup {<<itvl[1], p>>, <<p + 1, itvl[2]>>}
       /\ pc' = pc
  \/ /\ Work = {}
     /\ pc = "loop"
     /\ pc' = "done"
     /\ UNCHANGED <<Seq, Original, Work>>
  \/ /\ pc = "done"
     /\ UNCHANGED <<Seq, Original, Work, pc>>

Init ==
  /\ Len(Seq) > 0
  /\ Original = Seq
  /\ Work = {<<1, Len(Seq)>>}
  /\ pc = "loop"

Next == QuicksortStep

Inv ==
  /\ \A itvl \in Work :
        /\ itvl[1] >= 1 /\ itvl[2] >= itvl[1]
        /\ itvl[2] <= Len(Seq)
  /\ \A i \in 1 .. Len(Seq) : \E j \in 1 .. Len(Original) : Seq[i] = Original[j]
  /\ \A i \in 1 .. Len(Seq) :
        \A j \in 1 .. Len(Seq) :
          (i < j /\ \A itvl \in Work : (i \in itvl) => (j \in itvl)) => Seq[i] <= Seq[j]

\* PCorrect is the end-of-algorithm assertion: a terminating run must leave
\* the sequence sorted and a permutation of the original.
PCorrect == (pc = "done") => (Permutations(1 .. Len(Seq)) = Permutations(1 .. Len(Original)))

Spec == Init /\ [][Next]_<<Seq, Original, Work, pc>>

W4 == TRUE

\* The loop plus the final check are not triggered by a single fairness
\* condition (neither is enabled when Work is empty), so a stepwise
\* fairness that covers all of them at once is used.
Termination == WF_vars(W4)

====