---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

(* ----------------------------------------------------------------------
   LimitedSeq  – a finite version of Seq, limited by MaxSeqLen.
   ---------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

VARIABLES seq, orig, work, pc

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
IsPermutation(s, t) ==
  \A x \in Values :
    Cardinality({ j \in 1..Len(s) : s[j] = x }) =
    Cardinality({ j \in 1..Len(t) : t[j] = x })

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

PartitionResults(s, i, p) ==
  { s2 \in LimitedSeq(Values) :
      Len(s2) = Len(s) /\
      \A j \in 1..Len(s) :
        (j < i.lo \/ j > i.hi) => s2[j] = s[j] /\
      \A j1 \in i.lo..p, j2 \in p+1..i.hi : s2[j1] <= s2[j2] /\
      IsPermutation(s2, s) }

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

(* ----------------------------------------------------------------------
   Main sorting step
   ---------------------------------------------------------------------- *)
Main ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E i \in work :
        LET singleton == i.lo = i.hi
            pivots    == i.lo..i.hi
        IN
        \/ /\ singleton
           /\ seq' = seq
           /\ orig' = orig
           /\ work' = work \ {i}
           /\ pc' = "Loop"
        \/ /\ ~singleton
           /\ \E p \in pivots :
                 LET lower   == [lo |-> i.lo, hi |-> p]
                     upper   == IF p < i.hi THEN {[lo |-> p+1, hi |-> i.hi]} ELSE {}
                     newWork == (work \ {i}) \cup {lower} \cup upper
                 IN
                 /\ seq' \in PartitionResults(seq, i, p)
                 /\ orig' = orig
                 /\ work' = newWork
                 /\ pc' = "Loop"

(* ----------------------------------------------------------------------
   Termination step
   ---------------------------------------------------------------------- *)
Done ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work

(* ----------------------------------------------------------------------
   Stuttering after termination (prevents deadlock)
   ---------------------------------------------------------------------- *)
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ Main
  \/ Done
  \/ Stutter

Spec ==
  Init /\ [][Next]_<<seq, orig, work, pc>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(orig) = Len(seq)
  /\ work \subseteq [lo: Nat, hi: Nat]
  /\ \A i \in work :
        i.lo \in 1..Len(seq) /\ i.hi \in i.lo..Len(seq)
  /\ pc \in {"Loop", "Done"}

(* ----------------------------------------------------------------------
   Main invariant (preserves permutation and well‑formed intervals)
   ---------------------------------------------------------------------- *)
Inv ==
  /\ TypeOK
  /\ IsPermutation(seq, orig)
  /\ \A i \in work :
        i.lo \in 1..Len(seq) /\ i.hi \in i.lo..Len(seq)

(* ----------------------------------------------------------------------
   Partial correctness when algorithm terminates
   ---------------------------------------------------------------------- *)
PCorrect ==
  /\ pc = "Done"
  /\ Sorted(seq)
  /\ IsPermutation(seq, orig)

(* ----------------------------------------------------------------------
   Liveness property: eventual termination
   ---------------------------------------------------------------------- *)
Termination ==
  <> (pc = "Done")

====