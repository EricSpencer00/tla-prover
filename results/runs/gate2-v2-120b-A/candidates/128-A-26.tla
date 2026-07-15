---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants required by the .cfg file.
  Values : the set of integer values that may appear in the sequence.
  MaxSeqLen : the maximum length of the sequence (positive integer).
  Seq : a nondeterministically chosen initial sequence of length in 1..MaxSeqLen.
--------------------------------------------------------------------*)
CONSTANTS Values, MaxSeqLen, Seq

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Indices == 1 .. Len(Seq)

(* An interval is a pair <<i, j>> with i <= j and i,j in Indices *)
Interval == [lo : Nat, hi : Nat]

IsInterval(i) == /\ i \in Interval
                /\ i.lo \in Indices
                /\ i.hi \in Indices
                /\ i.lo <= i.hi

(* The set of all possible intervals over Indices *)
AllIntervals == { i \in [lo : Nat, hi : Nat] :
                  i.lo \in Indices /\ i.hi \in Indices /\ i.lo <= i.hi }

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES seq, origSeq, workSet, pc

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ seq = Seq
  /\ origSeq = Seq
  /\ workSet = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Running"

(*--------------------------------------------------------------------
  Partition operator (abstract, nondeterministic)
  For a given interval i and pivot position p (i.lo <= p <= i.hi),
  it returns a sequence seq2 such that:
    - Elements outside i are unchanged.
    - All elements with index <= p are <= every element with index > p.
    - seq2 is a permutation of seq.
--------------------------------------------------------------------*)
Partition(seq1, i, p) ==
  { seq2 \in [1..Len(seq1) -> Values] :
        /\ \A j \in Indices :
              (j < i.lo \/ j > i.hi) => seq2[j] = seq1[j]
        /\ \A j \in i.lo .. p, k \in (p+1) .. i.hi :
              seq2[j] <= seq2[k]
        /\ \A v \in Values :
              Cardinality({ j \in Indices : seq2[j] = v }) =
              Cardinality({ j \in Indices : seq1[j] = v }) }

(*--------------------------------------------------------------------
  Single iteration of the algorithm
--------------------------------------------------------------------*)
Step ==
  \/ /\ pc = "Running"
        /\ workSet # {}
        /\ \E i \in workSet :
            /\ IsInterval(i)
            /\ IF i.lo = i.hi
               THEN /\ workSet' = workSet \ {i}
                    /\ UNCHANGED <<seq, origSeq, pc>>
               ELSE
                 LET piv == i.lo + (i.hi - i.lo) % 2 \* a simple deterministic pivot (any in range)
                 IN
                 /\ \E seq2 \in Partition(seq, i, piv) :
                       /\ seq' = seq2
                       /\ workSet' = (workSet \ {i}) \cup
                                   { [lo |-> i.lo, hi |-> piv],
                                     [lo |-> piv+1, hi |-> i.hi] }
                 /\ UNCHANGED pc
  \/ /\ pc = "Running"
        /\ workSet = {}
        /\ pc' = "Done"
        /\ UNCHANGED <<seq, origSeq, workSet>>
  \/ /\ pc = "Done"
        /\ UNCHANGED <<seq, origSeq, workSet, pc>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next == Step

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, origSeq, workSet, pc>>

(*--------------------------------------------------------------------
  Safety invariant: permutation preservation
--------------------------------------------------------------------*)
Inv ==
  /\ \A v \in Values :
        Cardinality({ j \in Indices : seq[j] = v }) =
        Cardinality({ j \in Indices : origSeq[j] = v })
  /\ \A i \in workSet :
        IsInterval(i)

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in [Indices -> Values]
  /\ origSeq \in [Indices -> Values]
  /\ workSet \subseteq AllIntervals
  /\ pc \in {"Running", "Done"}

(*--------------------------------------------------------------------
  Partial correctness invariant asserted when the algorithm has terminated.
--------------------------------------------------------------------*)
PCorrect ==
  /\ pc = "Done"
  /\ \A i, j \in Indices : i < j => seq[i] <= seq[j]   \* sorted
  /\ Inv                                            \* permutation

(*--------------------------------------------------------------------
  Liveness property: termination
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================