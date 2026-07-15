---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants required by the .cfg file.
  Values : the domain of integer values that may appear in the sequence.
  MaxSeqLen : an upper bound on the length of the sequence (used only
              by the companion .cfg module that defines Seq).
  Seq : a nondeterministically chosen non‑empty sequence of values,
        whose length is bounded by MaxSeqLen.
-----------------------------------------------------------------*)
CONSTANTS Values, MaxSeqLen, Seq

(*-----------------------------------------------------------------
  Types (for readability; the actual type invariant is called TypeOK)
-----------------------------------------------------------------*)
Idx == 1 .. Len(Seq)

(* An interval is represented as a pair <<low, high>> with low <= high *)
Interval == [low: Idx, high: Idx]

\* The set of all possible intervals over the indices of the sequence
Intervals == { [low |-> i, high |-> j] : i \in Idx, j \in Idx, i <= j }

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES seq, origSeq, work, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
IsSingleton(itv) == itv.low = itv.high

(* A permutation of a sequence seq on a set of indices S, leaving all
   other positions unchanged. *)
PermutationOn(seq, S) ==
  \E perm \in [S -> S] :
    \A i \in S : seq[perm[i]] = seq[i] /\ \A i \notin S : seq[i] = seq[i]

(* A valid partition step for a chosen interval itv and pivot index p.
   - Elements outside itv stay unchanged.
   - Elements inside itv are permuted so that positions low..p contain
     only values less than or equal to any value that appears in
     positions p+1..high. *)
ValidPartition(seq, itv, p) ==
  \E new \in Seq(Values) :
    /\ \A i \in Idx : new[i] \in Values
    /\ \A i \in Idx : (i \notin itv.low .. itv.high) => new[i] = seq[i]
    /\ \A i \in itv.low .. p, j \in p+1 .. itv.high : new[i] <= new[j]
    /\ (\A i \in itv.low .. itv.high : \E j \in itv.low .. itv.high : new[i] = seq[j])
    /\ (\A i \in itv.low .. itv.high : \E j \in itv.low .. itv.high : seq[i] = new[j])

LowerInterval(itv, p) == [low |-> itv.low, high |-> p]
UpperInterval(itv, p) == [low |-> p+1, high |-> itv.high]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ seq = Seq
  /\ origSeq = Seq
  /\ work = { [low |-> 1, high |-> Len(Seq)] }
  /\ pc = "Loop"

(*-----------------------------------------------------------------
  The main transition relation
-----------------------------------------------------------------*)
LoopStep ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E itv \in work :
        (*
          1. If singleton, simply remove it from the work set.
        *)
        ( \/ /\ IsSingleton(itv)
             /\ work' = work \ {itv}
             /\ UNCHANGED <<seq, origSeq, pc>>
         \/ /\ ~IsSingleton(itv)
             /\ \E p \in itv.low .. itv.high :
                  /\ ValidPartition(seq, itv, p)
                  /\ LET newSeq == CHOOSE new \in Seq(Values) : ValidPartition(seq, itv, p) IN
                     /\ seq' = newSeq
                     /\ work' = (work \ {itv}) \cup { LowerInterval(itv, p), UpperInterval(itv, p) }
                     /\ UNCHANGED origSeq
                     /\ pc' = "Loop"
         )
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, origSeq, work>>

TerminationStep ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, origSeq, work, pc>>

Next == LoopStep \/ TerminationStep

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

(*-----------------------------------------------------------------
  Type invariant (helps TLC)
-----------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Values)
  /\ origSeq \in Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"Loop", "Done"}

(*-----------------------------------------------------------------
  Partial‑correctness invariant: when the algorithm has terminated,
  the sequence is a permutation of the original and is sorted.
-----------------------------------------------------------------*)
Sorted(seq) ==
  \A i, j \in Idx : i < j => seq[i] <= seq[j]

Permutation(seq1, seq2) ==
  \A i \in Idx : \E j \in Idx : seq1[i] = seq2[j]

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(seq, origSeq))

(*-----------------------------------------------------------------
  Full inductive invariant used for model checking.
-----------------------------------------------------------------*)
Inv == TypeOK /\ PCorrect

(*-----------------------------------------------------------------
  Liveness property required by the .cfg file.
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

====