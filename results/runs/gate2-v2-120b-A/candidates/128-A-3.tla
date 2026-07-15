---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, orig, work, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Idx == 1 .. Len(seq)

Interval == [lo : Nat, hi : Nat]
Dom == 1 .. MaxSeqLen

(* The domain of an interval is its set of indices *)
DomOf(iv) == iv.lo .. iv.hi

(* An interval is valid iff it lies within the current sequence length
   and lo <= hi *)
IntervalOK(iv) == iv \in Interval /\ iv.lo <= iv.hi /\ iv.hi <= Len(seq)

(* A permutation of the original sequence that respects a sub‑domain *)
PermPreservesOutside(new) ==
  \A i \in Idx :
    (i \notin DomOf(iv) => new[i] = seq[i])

(* Partition relation for a chosen pivot within an interval *)
Partition(iv, p) ==
  \E new \in Seq :
    /\ Len(new) = Len(seq)
    /\ \A i \in Idx :
         (i < iv.lo \/ i > iv.hi) => new[i] = seq[i]
    /\ p \in iv.lo .. iv.hi
    /\ \A i \in iv.lo .. p : \A j \in p+1 .. iv.hi : new[i] <= new[j]
    /\ Permutation(seq, new)

(* Permutation predicate – existence of a bijection on indices *)
Permutation(old, new) ==
  \E f \in [Idx -> Idx] :
    /\ \A i \in Idx : new[i] = old[f[i]]
    /\ \A i, j \in Idx : f[i] = f[j] => i = j

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ seq \in Seq
  /\ Len(seq) > 0
  /\ Len(seq) <= MaxSeqLen
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

(*-----------------------------------------------------------------
  Main action (one iteration of the sorting loop)
-----------------------------------------------------------------*)
Loop ==
  /\ pc = "Loop"
  /\ IF work = {} THEN
        /\ pc' = "Done"
        /\ UNCHANGED <<seq, orig, work>>
     ELSE
        /\ \E iv \in work :
              /\ IntervalOK(iv)
              /\ IF iv.lo = iv.hi THEN
                    /\ work' = work \ { iv }
                    /\ seq' = seq
                 ELSE
                    /\ \E p \in iv.lo .. iv.hi :
                          /\ \E new \in Seq :
                                /\ Len(new) = Len(seq)
                                /\ Partition(iv, p)
                                /\ seq' = new
                                /\ work' = (work \ { iv }) \cup
                                         { [lo |-> iv.lo, hi |-> p],
                                           [lo |-> p+1, hi |-> iv.hi] }
              /\ pc' = "Loop"
              /\ orig' = orig

(* Stuttering step after termination *)
Done ==
  /\ pc = "Done"
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

Next == Loop \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ Len(seq) = Len(orig)
  /\ Len(seq) <= MaxSeqLen
  /\ work \subseteq { iv \in Interval : iv.lo <= iv.hi /\ iv.hi <= Len(seq) }
  /\ pc \in {"Loop", "Done"}

(*-----------------------------------------------------------------
  Partial correctness invariant (permutation + sortedness)
-----------------------------------------------------------------*)
Inv ==
  /\ Permutation(orig, seq)
  /\ \A i, j \in Idx : i < j => seq[i] <= seq[j]

(*-----------------------------------------------------------------
  PCorrect – the safety condition required by the description
-----------------------------------------------------------------*)
PCorrect ==
  /\ pc = "Done"
  => Inv

(*-----------------------------------------------------------------
  Termination property (eventually reaching Done)
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================