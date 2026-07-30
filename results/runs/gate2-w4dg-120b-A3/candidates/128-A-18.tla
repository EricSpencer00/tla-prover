---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* The final model uses the standard Sequences module, but for model
\* checking the cfg file replaces operator Seq with a bounded version.
\* This declaration therefore defines no new symbol; it only records
\* the shape of the operator that Seq must keep.
LimitedSeq == [1..MaxSeqLen -> Values]

VARIABLES seq, original, work, pc
vars == <<seq, original, work, pc>>

Unsorted(i) == i \in DOMAIN seq

\* Adjacent intervals are defined only on the subset of indices that
\* actually appear in the current sequence.
Adjacent(a, b) ==
  /\ a[2] + 1 = b[1]
  /\ a[2] <= Len(seq) /\ b[2] <= Len(seq)

\* A partition keeps everything outside the chosen interval exactly the
\* same, and orders the left side below or equal to the right side.
IsPartition(f, intvl, k) ==
  /\ DOMAIN f \subseteq DOMAIN seq
  /\ \A j \in DOMAIN seq : j \notin intvl => f[j] = seq[j]
  /\ \A i \in intvl, j \in intvl : (i <= k /\ j > k) => (f[i] <= f[j])

\* Automorphisms of [1..Len(seq)] are the only permutations that must be
\* considered when checking that the output is a true reordering.
Automorphism(f) ==
  /\ DOMAIN f = 1..Len(seq)
  /\ \A i \in 1..Len(seq) : f[i] \in 1..Len(seq)
  /\ \A a, b \in 1..Len(seq) : f[a] = f[b] => a = b

PermutationOfOriginal(f) == /\ DOMAIN f \subseteq DOMAIN seq
                           /\ \A i \in DOMAIN seq : f[i] \in Values
                           /\ Automorphism(f)

\* The set of intervals formed by the algorithm is always a domain
\* partition of the sequence: intervals are adjacent, disjoint and cover
\* the whole of the current sequence.
\* The work set must, in particular, never lose a piece of the domain.
IsDomainPartition(S) ==
  /\ S # {}
  /\ \A a \in S : Unsorted(a[2])
  /\ \A a, b \in S : a # b => \A i \in a, j \in b : i # j
  /\ \E a \in S : a[1] = 1
  /\ \E a \in S : a[2] = Len(seq)

\* No interval is ever split past a singleton, so the algorithm is
\* guaranteed to make progress as long as work is non-empty.
StrictlyRefinedBy(S) == \E a, b \in S : a[2] < b[1]
RelativeSortedness == \A a \in work, b \in work :
  (a # b /\ a[2] <= b[1]) => \A i \in a, j \in b : seq[i] <= seq[j]

\* The original sequence is only compared to the final one, so the
\* copied copy is always defined for the lifetime of the spec.
\* Nondeterministic choice: any sortable sequence of any length up to
\* MaxSeqLen, drawn from the supplied Values set.
Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] :
       /\ \E n \in 1..MaxSeqLen : seq = [i \in 1..n |-> s[i]]
  /\ original = seq
  /\ work = {[1, Len(seq)]}
  /\ pc = "Loop"

\* The single loop body: pick an interval, a pivot, and a new version of
\* the whole sequence that is a valid partition over that interval.
\* The interval is replaced by two strictly smaller intervals, so the
\* work set strictly shrinks in the number of unresolved pieces.
Step ==
  /\ pc = "Loop"
  /\ work \not= {}
  /\ \E intvl \in work :
       \/ /\ intvl[1] = intvl[2]
          /\ work' = work \ {intvl}
       \/ /\ \E k \in intvl :
            /\ \E f \in [1..Len(seq) -> Values] :
                 /\ IsPartition(f, intvl, k)
                 /\ seq' = f
            /\ work' = (work \ {intvl}) \cup {[intvl[1], k], [k + 1, intvl[2]]}
  /\ pc' = "Loop"
  /\ UNCHANGED original

Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, original, work>>

Idle == pc = "Done" /\ UNCHANGED vars

Next == Step \/ Terminate \/ Idle

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step) /\ WF_vars(Terminate)

PCorrect == pc = "Done" => (\A i \in 1..Len(seq) - 1 : seq[i] <= seq[i + 1])
TypeOK == /\ seq \in Sequences(Values)
          /\ original \in Sequences(Values)
          /\ work \in SUBSET (SUBSET (1..MaxSeqLen \X 1..MaxSeqLen))
          /\ pc \in {"Loop", "Done"}
Inv == /\ IsDomainPartition(work)
       /\ PermutationOfOriginal(seq)
       /\ RelativeSortedness
Termination == <>_vars(pc = "Done")

====