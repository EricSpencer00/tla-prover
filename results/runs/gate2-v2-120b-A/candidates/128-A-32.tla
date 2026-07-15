---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants required by the cfg file
--------------------------------------------------------------------*)
CONSTANTS Values, MaxSeqLen, Seq

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* Domain of indices for sequences of length at most MaxSeqLen
Idx == 1 .. MaxSeqLen

\* An interval is a pair <<l, u>> with l <= u and both in Idx
Interval == { <<l, u>> \in Idx \X Idx : l <= u }

\* A subinterval selection operator (used to compute new intervals)
SubIntervals(i) ==
  LET l == i[1] IN
  LET u == i[2] IN
  { <<l, p-1>> \in Interval : p \in l..u } \cup
  { <<p+1, u>> \in Interval : p \in l..u }

\* Permutation: a bijection on the domain of values
Permutation == { f \in [Values -> Values] : \A x \in Values : \E y \in Values : f[y] = x }

\* Apply a permutation to a sequence (only elements inside the interval
\* may be permuted; elements outside stay unchanged)
ApplyPerm(s, perm, i) ==
  LET l == i[1] IN
  LET u == i[2] IN
  [j \in Idx |->
     IF j \in l..u
        THEN perm[s[j]]
        ELSE s[j]]

\* A valid partition step: choose a pivot p in the interval and a
\* permutation perm that respects the partition ordering.
Partition(s, i) ==
  \E p \in i[1]..i[2] :
    \E perm \in Permutation :
      /\ \A j \in i[1]..i[2] : s[p] <= perm[s[j]]  \/  perm[s[j]] <= s[p]
         \* (All elements are either <= pivot element or >= it)
      /\ \A j \in Idx \ i[1]..i[2] : perm[s[j]] = s[j]
         \* Outside the interval nothing changes
      /\ ApplyPerm(s, perm, i)

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ seq = Seq
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc   = "Loop"

(*--------------------------------------------------------------------
  The main iteration action
--------------------------------------------------------------------*)
LoopStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E i \in work :
       LET l == i[1] IN
       LET u == i[2] IN
       IF l = u
          THEN /\ seq' = seq
               /\ work' = work \ {i}
               /\ pc'   = pc
          ELSE /\ \E p \in l..u :
                 /\ seq' = Partition(seq, i)
               /\ work' = (work \ {i}) \cup { <<l, p-1>>, <<p+1, u>> }
               /\ pc'   = pc

(*--------------------------------------------------------------------
  Termination step
--------------------------------------------------------------------*)
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

(*--------------------------------------------------------------------
  Stuttering after termination
--------------------------------------------------------------------*)
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  LoopStep \/ Terminate \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  TypeOK invariant (helps TLC)
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in [Idx -> Values]
  /\ orig \in [Idx -> Values]
  /\ work \subseteq Interval
  /\ pc \in {"Loop", "Done"}

(*--------------------------------------------------------------------
  Partial correctness invariant: when done, seq is a sorted permutation
  of orig.
--------------------------------------------------------------------*)
Sorted(s) ==
  \A i, j \in Idx : i < j => s[i] <= s[j]

Permutes(s, o) ==
  \A v \in Values : Cardinality({i \in Idx : s[i] = v}) =
                    Cardinality({i \in Idx : o[i] = v})

PCorrect ==
  (pc = "Done") => /\ Sorted(seq)
                    /\ Permutes(seq, orig)

(*--------------------------------------------------------------------
  Full invariant used for model checking
--------------------------------------------------------------------*)
Inv == PCorrect /\ TypeOK

(*--------------------------------------------------------------------
  Liveness property: termination
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================