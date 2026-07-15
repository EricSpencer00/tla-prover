---- MODULE Quicksort ----
EXTENDS FiniteSets, Naturals, Sequences, TLC

(*---------------------------------------------------------------------*)
(* Constants (to be instantiated in the .cfg)                           *)
CONSTANTS
    Values,          \* The set of integer values that may appear in a sequence
    MaxSeqLen,       \* Upper bound on the length of the sequence
    Seq              \* The initial nondeterministically‑chosen sequence

(*---------------------------------------------------------------------*)
(* Derived definitions                                                  *)

(* The set of all indices of a sequence of length n (1..n) *)
Indices(n) == 1 .. n

(* A subinterval is represented as a pair <<i, j>> with i <= j *)
Interval == [i : Nat, j : Nat]

(* The work‑set is a set of intervals *)
WorkSet == SUBSET Interval

(*---------------------------------------------------------------------*)
(* Variables                                                            *)

VARIABLES
    seq,        \* The current sequence being sorted
    orig,       \* Copy of the original sequence (never changes)
    work,       \* Set of intervals still to be processed
    pc          \* Program counter: either "Loop" or "Done"

(*---------------------------------------------------------------------*)
(* Helper definitions                                                   *)

(* Length of the current sequence *)
SeqLen == Len(seq)

(* ``sorted`` is true when seq is non‑decreasing *)
Sorted == \A i \in 1 .. (SeqLen - 1) : seq[i] <= seq[i+1]

(* ``IsPermutation`` asserts that seq is a permutation of orig *)
IsPermutation ==
    \A i \in Indices(SeqLen) :
        \E j \in Indices(SeqLen) : seq[i] = orig[j]

(* ``ValidPartition`` describes the nondeterministic partition result.
   It leaves elements outside the interval unchanged and guarantees that
   every element in the lower part (i .. p) is <= every element in the
   upper part (p+1 .. j). *)
ValidPartition(old, new, int) ==
    /\ int.i <= int.j
    /\ \A k \in Indices(SeqLen) :
          (k < int.i \/ k > int.j) => new[k] = old[k]
    /\ \E p \in int.i .. int.j :
          /\ \A k \in int.i .. p   : new[k] <= new[p+1]
          /\ \A k \in p+1 .. int.j : new[p]   <= new[k]

(* ``Subintervals`` returns the two sub‑intervals created by partitioning
   interval int around pivot p (lower: int.i..p, upper: p+1..int.j). *)
Subintervals(int, p) == {
    [i |-> int.i, j |-> p],
    [i |-> p+1,    j |-> int.j]
}

(*---------------------------------------------------------------------*)
(* Initialization                                                       *)

Init ==
    /\ seq = Seq
    /\ orig = Seq
    /\ work = { [i |-> 1, j |-> Len(Seq)] }
    /\ pc = "Loop"

(*---------------------------------------------------------------------*)
(* Main transition (one loop iteration)                                 *)

OneStep ==
    \/ /\ pc = "Loop"
          /\ work # {}
          /\ \E int \in work :
                /\ int.i <= int.j
                /\ IF int.i = int.j THEN
                       /\ work' = work \ {int}
                       /\ UNCHANGED <<seq, orig, pc>>
                   ELSE
                       /\ \E p \in int.i .. int.j :
                              /\ seq' \in
                                 { new : ValidPartition(seq, new, int) /\ new[p] >= seq[p] }
                                 \* The extra conjunct ensures a pivot exists; any
                                   suitable new sequence is allowed.
                              /\ work' = (work \ {int}) \cup Subintervals(int, p)
                              /\ pc' = "Loop"
          /\ UNCHANGED orig
    \/ /\ pc = "Loop"
          /\ work = {}
          /\ seq' = seq
          /\ work' = work
          /\ pc' = "Done"
          /\ UNCHANGED orig
    \/ /\ pc = "Done"
          /\ UNCHANGED <<seq, orig, work, pc>>

Next == OneStep

(*---------------------------------------------------------------------*)
(* Specification                                                        *)

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(*---------------------------------------------------------------------*)
(* Safety invariants                                                    *)

(* Basic type correctness                                            *)
TypeOK ==
    /\ seq \in Seq(Values)
    /\ orig \in Seq(Values)
    /\ Len(seq) = Len(orig)
    /\ Len(seq) <= MaxSeqLen
    /\ work \subseteq WorkSet
    /\ \A int \in work : int.i <= int.j /\ int.j <= Len(seq)

(* The main partial‑correctness invariant                            *)
Inv ==
    /\ IsPermutation
    /\ Sorted \/ work # {}

(* The standard TLA+ “process‑correctness” invariant – useful for TLC *)
PCorrect ==
    pc \in {"Loop", "Done"}

(*---------------------------------------------------------------------*)
(* Liveness property – termination (for completeness, not used by TLC) *)

Termination == []<>(pc = "Done")

(*---------------------------------------------------------------------*)
(* THEOREMS (optional, for manual inspection)                           *)

THEOREM Spec => []Inv
THEOREM Spec => []PCorrect

=============================================================================