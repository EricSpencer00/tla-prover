---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

(* ---------------------------------------------------------------------- *)
(*  Operator that limits the standard Seq operator to sequences of length
    at most MaxSeqLen and non‑empty, so that the model is finite.            *)
LimitedSeq(V, N) == { s \in Seq(V) : Len(s) \in 1..N }

(* ---------------------------------------------------------------------- *)
VARIABLES seq, orig, work, pc
vars == << seq, orig, work, pc >>

(* ---------------------------------------------------------------------- *)
(*  Helper definitions *)

Domain(s) == DOMAIN s

Count(s, v) ==
  Cardinality({ i \in Domain(s) : s[i] = v })

Permutation(s1, s2) ==
  \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Interval == <<i, j>> \in (1..Len(seq)) \X (1..Len(seq)) /\ i <= j

Intervals ==
  { <<i, j>> : i \in 1..Len(seq), j \in i..Len(seq) }

(* ---------------------------------------------------------------------- *)
(*  Partition operator: all sequences obtainable by a valid partition of
    the interval [lo..hi] around pivot p.                                    *)
Partition(s, lo, hi, p) ==
  { s' \in LimitedSeq(Values, MaxSeqLen) :
      /\ Len(s') = Len(s)
      /\ (\A i \in 1..Len(s) : (i < lo \/ i > hi) => s'[i] = s[i])
      /\ (\A i \in lo..p : \A j \in p+1..hi : s'[i] <= s'[j])
      /\ Permutation(s, s')
  }

(* ---------------------------------------------------------------------- *)
(*  Initial state *)
Init ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

(* ---------------------------------------------------------------------- *)
(*  Main step of the algorithm *)
LoopStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E I \in work :
        LET lo == I[1] IN
        LET hi == I[2] IN
        IF lo = hi THEN
          /\ seq' = seq
          /\ orig' = orig
          /\ work' = work \ { I }
          /\ pc' = "Loop"
        ELSE
          /\ \E p \in lo..hi :
               \E newSeq \in Partition(seq, lo, hi, p) :
                 /\ seq' = newSeq
                 /\ orig' = orig
                 /\ work' = (work \ { I }) \cup { <<lo, p>>, <<p+1, hi>> }
                 /\ pc' = "Loop"

(* ---------------------------------------------------------------------- *)
(*  Transition to the terminated state *)
DoneStep ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

(* ---------------------------------------------------------------------- *)
(*  Stuttering after termination, to avoid deadlock *)
StutterStep ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  LoopStep \/ DoneStep \/ StutterStep

(* ---------------------------------------------------------------------- *)
(*  Specification *)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

(* ---------------------------------------------------------------------- *)
(*  Type invariant *)
TypeOK ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig \in LimitedSeq(Values, MaxSeqLen)
  /\ work \subseteq Intervals
  /\ pc \in {"Loop", "Done"}

(* ---------------------------------------------------------------------- *)
(*  Invariant used in the proof (here we simply reuse TypeOK) *)
Inv == TypeOK

(* ---------------------------------------------------------------------- *)
(*  Partial‑correctness property: when the algorithm terminates the
    resulting sequence is sorted and a permutation of the original. *)
PCorrect ==
  (pc = "Done") => /\ Sorted(seq) /\ Permutation(seq, orig)

(* ---------------------------------------------------------------------- *)
(*  Liveness property: the algorithm eventually terminates *)
Termination == <> (pc = "Done")

====