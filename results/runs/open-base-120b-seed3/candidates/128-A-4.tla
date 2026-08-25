---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Count(seq, v) ==
  Cardinality({ i \in 1..Len(seq) : seq[i] = v })

IsPermutation(s1, s2) ==
  \A v \in Values : Count(s1, v) = Count(s2, v)

IsSorted(seq) ==
  \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= MaxSeqLen }

(* Intervals are represented as ordered pairs <<low,high>> *)
Low(iv) == iv[1]
High(iv) == iv[2]

InInterval(i, iv) == Low(iv) <= i /\ i <= High(iv)

IsSingleton(iv) == Low(iv) = High(iv)

(* PartitionResult captures the abstract effect of a correct partition *)
PartitionResult(seq, iv, p, newSeq) ==
  /\ Len(newSeq) = Len(seq)
  /\ \A i \in 1..Len(seq) :
        IF ~InInterval(i, iv) THEN newSeq[i] = seq[i] ELSE TRUE
  /\ \A i \in Low(iv)..p : newSeq[i] <= newSeq[p]
  /\ \A i \in p+1..High(iv) : newSeq[i] >= newSeq[p]
  /\ \A v \in Values : Count(newSeq, v) = Count(seq, v)

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

(*-----------------------------------------------------------------
  Type invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq { <<i, j>> : i \in 1..Len(seq) /\ j \in i..Len(seq) }
  /\ pc \in {"Loop", "Done"}

(*-----------------------------------------------------------------
  Global invariant
-----------------------------------------------------------------*)
Inv ==
  /\ TypeOK
  /\ IsPermutation(seq, orig)
  /\ \A iv \in work :
        /\ Low(iv) >= 1
        /\ High(iv) <= Len(seq)
        /\ Low(iv) <= High(iv)

(*-----------------------------------------------------------------
  Partial‑correctness condition
-----------------------------------------------------------------*)
PCorrect ==
  (pc = "Done") => (IsSorted(seq) /\ IsPermutation(seq, orig))

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E iv \in work :
          IF IsSingleton(iv) THEN
            /\ work' = work \ {iv}
            /\ seq' = seq
            /\ orig' = orig
            /\ pc' = pc
          ELSE
            /\ \E p \in Low(iv)..High(iv) :
                 /\ \E newSeq \in LimitedSeq(Values) :
                      /\ PartitionResult(seq, iv, p, newSeq)
                      /\ seq' = newSeq
                      /\ work' = (work \ {iv}) \cup { <<Low(iv), p>>, <<p+1, High(iv)>> }
                      /\ orig' = orig
                      /\ pc' = pc
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================