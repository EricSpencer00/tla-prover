---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

(* ------------------------------------------------------------------- *)
(* Helper definitions *)
NatSeq(i) == [i \in 1..MaxSeqLen |-> Seq[i]]

SeqDomain == 1..MaxSeqLen

SeqSet == { s \in Seq : Len(s) <= MaxSeqLen }

(* Permutation defined via bijection on domain of a sequence *)
Permutes(s, t) ==
  \E f \in [SeqDomain -> SeqDomain] :
    /\ \A i \in SeqDomain : s[i] = t[f[i]]
    /\ \A i, j \in SeqDomain : (f[i] = f[j]) => i = j
    /\ \A i \in SeqDomain : i \notin 1..Len(s) => f[i] = i

(* Interval is a contiguous range of indices *)
Interval == [low : Nat, high : Nat] \* inclusive bounds

(* Set of intervals *)
WorkSet == SUBSET Interval

(* ------------------------------------------------------------------- *)
VARIABLES seq, orig, work, pc

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ seq \in SeqSet
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

(* ------------------------------------------------------------------- *)
(* Partition operator: nondeterministically choose a new sequence that
   is a valid partition of the current interval with respect to a pivot. *)
Partition(s, intv, piv) ==
  \E s2 \in SeqSet :
    /\ (\A i \in 1..Len(s) : i < intv.low \/ i > intv.high => s2[i] = s[i])
    /\ (\A i \in intv.low .. piv :
        \A j \in piv+1 .. intv.high :
          s2[i] <= s2[j])
    /\ Permutes(s, s2)

(* ------------------------------------------------------------------- *)
(* One iteration of the sorting loop *)
LoopStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E intv \in work :
        IF intv.low = intv.high
        THEN /\ work' = work \ {intv}
              /\ UNCHANGED <<seq, orig>>
        ELSE
          /\ \E piv \in intv.low .. intv.high :
                /\ seq' = Partition(seq, intv, piv)
                /\ work' = (work \ {intv}) \cup
                          { [low |-> intv.low,  high |-> piv],
                            [low |-> piv+1,    high |-> intv.high] }
                /\ UNCHANGED orig
  /\ pc' = "Loop"

(* ------------------------------------------------------------------- *)
(* Termination step *)
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

(* Stuttering after termination *)
DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  LoopStep \/ Terminate \/ DoneStutter

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(* ------------------------------------------------------------------- *)
(* Typedness invariant *)
TypeOK ==
  /\ seq \in SeqSet
  /\ orig \in SeqSet
  /\ work \subseteq {[low : Nat, high : Nat] : low <= high /\ low >= 1 /\ high <= MaxSeqLen}
  /\ pc \in {"Loop", "Done"}

(* ------------------------------------------------------------------- *)
(* Partial correctness invariant: when done, seq is sorted and a permutation of orig *)
Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutes(orig, seq))

(* ------------------------------------------------------------------- *)
(* Full invariant used for model checking *)
Inv ==
  /\ TypeOK
  /\ (pc = "Done") => (Sorted(seq) /\ Permutes(orig, seq))

(* ------------------------------------------------------------------- *)
(* Safety properties *)
Termination ==
  <>[](pc = "Done")

====