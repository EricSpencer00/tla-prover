---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*=============================================================================
  Constants (to be instantiated in the .cfg file)
  ===========================================================================*)
CONSTANTS Values, MaxSeqLen, Seq

(*=============================================================================
  Helper definitions
  ===========================================================================*)

(* The set of all non‑empty integer sequences of length ≤ MaxSeqLen drawn from Values *)
AllSeqs ==
  { s \in Seq(Values) : Len(s) > 0 /\ Len(s) <= MaxSeqLen }

(* The domain of indices for a given sequence s (1‑based, as in the Sequences module) *)
Dom(s) == 1 .. Len(s)

(* The type predicate for the algorithm's state *)
SortType == 
  /\ seq \in Seq(Values) /\ Len(seq) > 0 /\ Len(seq) <= MaxSeqLen
  /\ orig \in Seq(Values) /\ Len(orig) = Len(seq)
  /\ work \subseteq SUBSET(Intervals(seq))
  /\ pc \in {"Running", "Done"}

(* An interval is a pair <<i, j>> with 1 ≤ i ≤ j ≤ Len(seq) *)
Interval == [low: Nat, high: Nat]

(* The set of all possible intervals for a given sequence s *)
Intervals(s) == { [low |-> i, high |-> j] : i \in 1..Len(s), j \in i..Len(s) }

(* Permutation predicate: two sequences contain the same multiset of values *)
Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Values :
        Cardinality({ i \in 1..Len(s) : s[i] = v }) =
        Cardinality({ i \in 1..Len(t) : t[i] = v })

(* Non‑decreasing order predicate for a sequence *)
Sorted(s) ==
  \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

(*=============================================================================
  Variables
  ===========================================================================*)
VARIABLES seq, orig, work, pc

(*=============================================================================
  Initial predicate
  ===========================================================================*)
Init ==
  /\ seq \in AllSeqs
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Running"
  /\ SortType

(*=============================================================================
  Actions
  ===========================================================================*)

(* Remove a singleton interval from the work set *)
RemoveSingleton ==
  \E int \in work :
    /\ int.low = int.high
    /\ work' = work \ {int}
    /\ UNCHANGED <<seq, orig, pc>>

(* Perform one partition step on a non‑singleton interval *)
PartitionStep ==
  \E int \in work :
    /\ int.low < int.high
    /\ \E pivot \in int.low .. int.high :
        LET
          lowInt  == [low |-> int.low,  high |-> pivot-1]
          highInt == [low |-> pivot+1, high |-> int.high]
          newWork == (work \ {int}) \cup {lowInt, highInt}
          newSeq  == [i \in 1..Len(seq) |-> 
                       IF i \notin int.low..int.high THEN seq[i]
                       ELSE 
                         (* nondeterministically pick a value that respects the
                            partition property: elements left of pivot ≤ pivot element,
                            elements right of pivot ≥ pivot element *)
                         IF i <= pivot THEN
                           CHOOSE v \in Values :
                              /\ v <= seq[pivot]
                              /\ v \in { seq[j] : j \in int.low..int.high }
                         ELSE
                           CHOOSE v \in Values :
                              /\ v >= seq[pivot]
                              /\ v \in { seq[j] : j \in int.low..int.high }] 
        IN
          /\ work' = newWork
          /\ seq'  = newSeq
          /\ UNCHANGED <<orig, pc>>
          /\ /\ Permutation(seq, seq')
             /\ \A i \in int.low..int.high :
                    (i <= pivot => seq'[i] <= seq'[pivot]) /\
                    (i > pivot  => seq'[i] >= seq'[pivot])

(* Termination step: when work set is empty, move to Done state *)
Terminate ==
  /\ work = {}
  /\ pc = "Running"
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

(* Stuttering step after termination to avoid deadlock *)
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

(* The next-state relation *)
Next ==
  \/ RemoveSingleton
  \/ PartitionStep
  \/ Terminate
  \/ Stutter

(*=============================================================================
  Specification
  ===========================================================================*)
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(*=============================================================================
  Invariants
  ===========================================================================*)

(* Type correctness *)
TypeOK ==
  SortType

(* Safety invariant required by the description:
   - The work set always contains intervals that are subsets of the domain.
   - The sequence is always a permutation of the original.
   - All elements that have left the work set are already correctly placed
     relative to each other (i.e., no element to the left of a finished interval
      is greater than any element to its right).  The latter is expressed
      indirectly via the existence of a permutation that would be sorted
      if the algorithm were to finish. *)
Inv ==
  /\ work \subseteq Intervals(seq)
  /\ Permutation(seq, orig)
  /\ \A i, j \in 1..Len(seq) :
        (\A int \in work :
            (i \in int.low..int.high) => (j \notin int.low..int.high)) =>
        (i < j => seq[i] <= seq[j])

(* Partial‑correctness invariant: when the algorithm has terminated,
   the sequence is sorted and is a permutation of the original. *)
PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

(*=============================================================================
  Derived operators for the .cfg file
  ===========================================================================*)
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect

=============================================================================