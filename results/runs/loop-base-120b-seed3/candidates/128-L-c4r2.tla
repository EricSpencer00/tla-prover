---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Naturals, Integers

CONSTANTS Values, MaxSeqLen

(*---------------------------------------------------------------------*)
(* Types and helper definitions                                         *)
(*---------------------------------------------------------------------*)

(* LimitedSeq is a finite subset of the full sequence set, bounded by
   MaxSeqLen.  It replaces the unrestricted Seq operator for model
   checking. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Interval == [lo : Nat, hi : Nat]

Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

(*---------------------------------------------------------------------*)
(* Variables                                                            *)
(*---------------------------------------------------------------------*)

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

(*---------------------------------------------------------------------*)
(* Initial state                                                        *)
(*---------------------------------------------------------------------*)

Init ==
  /\ seq \in LimitedSeq(Values) /\ seq # <<>>
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

(*---------------------------------------------------------------------*)
(* Partition operator (nondeterministic choice)                         *)
(*---------------------------------------------------------------------*)

Partition(oldSeq, I, pivot) ==
  { newSeq \in LimitedSeq(Values) :
      /\ Len(newSeq) = Len(oldSeq)
      /\ \A i \in 1..Len(oldSeq) :
           (i < I.lo \/ i > I.hi) => newSeq[i] = oldSeq[i]
      /\ \A i \in I.lo..pivot :
           \A j \in pivot+1..I.hi : newSeq[i] <= newSeq[j] }

(*---------------------------------------------------------------------*)
(* Next-state relation                                                   *)
(*---------------------------------------------------------------------*)

Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E I \in work :
          IF I.lo = I.hi THEN
            /\ work' = work \ {I}
            /\ UNCHANGED <<seq, orig, pc>>
          ELSE
            /\ \E pivot \in I.lo..I.hi :
                 LET lower == [lo |-> I.lo, hi |-> pivot-1] IN
                 LET upper == [lo |-> pivot+1, hi |-> I.hi] IN
                 LET newWork ==
                       (work \ {I})
                     \cup (IF lower.lo <= lower.hi THEN {lower} ELSE {})
                     \cup (IF upper.lo <= upper.hi THEN {upper} ELSE {})
                 IN
                 /\ seq' \in Partition(seq, I, pivot)
                 /\ orig' = orig
                 /\ work' = newWork
                 /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

(*---------------------------------------------------------------------*)
(* Specification                                                         *)
(*---------------------------------------------------------------------*)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*---------------------------------------------------------------------*)
(* Invariants                                                            *)
(*---------------------------------------------------------------------*)

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq { I \in Interval : I.lo <= I.hi /\ I.hi <= Len(seq) }
  /\ pc \in {"Loop", "Done"}

Inv == TypeOK /\ Permutation(seq, orig)

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

(*---------------------------------------------------------------------*)
(* Liveness property                                                     *)
(*---------------------------------------------------------------------*)

Termination == []<>(pc = "Done")

=============================================================================