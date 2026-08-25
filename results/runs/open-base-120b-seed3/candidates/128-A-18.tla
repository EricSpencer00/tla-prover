---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

(*-------------------------------------------------------------------*)
(* Helper definitions *)

LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen /\ Len(s) > 0 }

InInterval(i, int) == int[1] <= i /\ i <= int[2]

AllIntervals == { <<l, h>> : l \in Nat /\ h \in Nat /\ l <= h }

SeqIntervals == { <<l, h>> : l \in 1..Len(seq) /\ h \in 1..Len(seq) /\ l <= h }

Count(v, s) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s1, s2) ==
    \A v \in Values : Count(v, s1) = Count(v, s2)

Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Partition(oldSeq, int, p) ==
    { newSeq \in Seq(Values) :
        /\ Len(newSeq) = Len(oldSeq)
        /\ \A i \in 1..Len(oldSeq) :
              ( ~InInterval(i, int) ) => newSeq[i] = oldSeq[i]
        /\ \A i, j \in 1..Len(oldSeq) :
              ( InInterval(i, int) /\ InInterval(j, int) /\ i <= p /\ j > p )
                 => newSeq[i] <= newSeq[j]
        /\ Permutation(newSeq, oldSeq) }

(*-------------------------------------------------------------------*)
(* Initial predicate *)

Init ==
    /\ seq \in LimitedSeq(Values)
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

(*-------------------------------------------------------------------*)
(* Actions *)

SingletonCase ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E int \in work : int[1] = int[2]
    /\ work' = work \ {int}
    /\ seq' = seq
    /\ orig' = orig
    /\ pc' = "Loop"

PartitionCase ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E int \in work : int[1] < int[2]
    /\ \E p \in int[1]..int[2] :
         /\ \E newSeq \in Partition(seq, int, p) :
              /\ seq' = newSeq
              /\ work' = (work \ {int}) \cup { <<int[1], p>>, <<p+1, int[2]>> }
              /\ orig' = orig
              /\ pc' = "Loop"

FinishStep ==
    /\ pc = "Loop"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

StepLoop == SingletonCase \/ PartitionCase

Next == StepLoop \/ FinishStep \/ Stutter

(*-------------------------------------------------------------------*)
(* Specification *)

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(*-------------------------------------------------------------------*)
(* Invariants *)

TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq SeqIntervals
    /\ pc \in {"Loop", "Done"}

Inv == /\ TypeOK
       /\ Permutation(seq, orig)

PCorrect == pc = "Done" => (Sorted(seq) /\ Permutation(seq, orig))

(*-------------------------------------------------------------------*)
(* Liveness property *)

Termination == <> (pc = "Done")

====