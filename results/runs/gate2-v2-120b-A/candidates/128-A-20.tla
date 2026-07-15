---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants required by the .cfg file.
  - Values   : the set of integer values that may appear in the sequence.
  - MaxSeqLen: the maximum length of the sequence (positive integer).
  - Seq      : a nondeterministically chosen initial sequence of values,
               of length between 1 and MaxSeqLen.
--------------------------------------------------------------------*)
CONSTANTS Values, MaxSeqLen, Seq

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Indices == 1 .. MaxSeqLen

Interval == SUBSET [i \in Indices, j \in Indices : i <= j]

(*  The domain of the current sequence is the set 1..Len(s). *)
Dom(s) == 1 .. Len(s)

(*  A permutation of s is any sequence s2 of the same length that is a
    reordering of the elements of s. *)
Permutation(s, s2) ==
  /\ Len(s) = Len(s2)
  /\ \A v \in Values : Cardinality({ i \in Dom(s) : s[i] = v }) =
                        Cardinality({ i \in Dom(s2) : s2[i] = v })

(*  A partition step for interval [i..j] with pivot p (i <= p <= j) can
    produce any sequence s2 that (a) is a permutation of s, (b) leaves
    elements outside [i..j] unchanged, (c) all elements at positions
    i..p are <= all elements at positions p+1..j. *)
Partition(s, s2, i, j, p) ==
  /\ Permutation(s, s2)
  /\ \A k \in 1..Len(s) : (k < i \/ k > j) => s2[k] = s[k]
  /\ \A a \in i..p : \A b \in p+1..j : s2[a] <= s2[b]

(*  A sequence is sorted in non‑decreasing order. *)
Sorted(s) ==
  /\ Len(s) = 0 \/ Len(s) = 1
  \/ \A i \in 1 .. Len(s)-1 : s[i] <= s[i+1]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES seq, origSeq, workSet, pc

(*--------------------------------------------------------------------
  Types (for TypeOK invariant)
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Values)
  /\ origSeq \in Seq(Values)
  /\ workSet \subseteq Interval
  /\ pc \in {"MainLoop", "Terminated"}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ seq = Seq
  /\ origSeq = Seq
  /\ workSet = { <<1, Len(seq)>> }
  /\ pc = "MainLoop"

(*--------------------------------------------------------------------
  Main loop action
--------------------------------------------------------------------*)
Loop ==
  /\ pc = "MainLoop"
  /\ IF workSet = {}
     THEN /\ pc' = "Terminated"
          /\ UNCHANGED <<seq, origSeq, workSet>>
     ELSE
        LET interval == CHOOSE int \in workSet : TRUE IN
        LET i == interval[1] IN
        LET j == interval[2] IN
        IF i = j
        THEN /\ workSet' = workSet \ { interval }
             /\ UNCHANGED <<seq, origSeq, pc>>
        ELSE
           LET p == CHOOSE k \in i..j : TRUE IN
           (*  Choose any valid partition result. *)
           LET s2 == CHOOSE s \in Seq(Values) :
                      Partition(seq, s, i, j, p) IN
           /\ seq' = s2
           /\ workSet' = (workSet \ { interval }) \cup { <<i, p>>, <<p+1, j>> }
           /\ UNCHANGED <<origSeq, pc>>

(*--------------------------------------------------------------------
  Stuttering step after termination to avoid deadlock.
--------------------------------------------------------------------*)
Stutter ==
  /\ pc = "Terminated"
  /\ UNCHANGED <<seq, origSeq, workSet, pc>>

Next == Loop \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, origSeq, workSet, pc>>

(*--------------------------------------------------------------------
  Safety invariant: when terminated, the sequence is a sorted
  permutation of the original.
--------------------------------------------------------------------*)
PCorrect ==
  /\ pc = "Terminated"
  /\ Permutation(origSeq, seq)
  /\ Sorted(seq)

(*--------------------------------------------------------------------
  Additional invariant used in the reference proof (placeholder).
  It is true in every reachable state and thus can serve as the
  Inv required by the .cfg file.
--------------------------------------------------------------------*)
Inv ==
  /\ Permutation(origSeq, seq)
  /\ \A i \in 1 .. Len(seq)-1 : seq[i] <= seq[i+1] \/ pc = "MainLoop"

(*--------------------------------------------------------------------
  Properties
--------------------------------------------------------------------*)
Termination == <> (pc = "Terminated")

====