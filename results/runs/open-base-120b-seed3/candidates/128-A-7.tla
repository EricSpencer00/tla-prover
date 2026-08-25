---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

(*-----------------------------------------------------------------
   LimitedSeq: a finite version of Seq that only allows sequences
   up to MaxSeqLen elements.
-----------------------------------------------------------------*)
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

(*-----------------------------------------------------------------
   Helper definitions
-----------------------------------------------------------------*)
Interval == [low : Nat, high : Nat]

Intervals(s) == { i \in [low : 1..Len(s), high : 1..Len(s)] : i.low <= i.high }

IsSingleton(i) == i.low = i.high

Count(s, i, v) ==
  Cardinality({ k \in i.low..i.high : s[k] = v })

PermPreserve(s, t, i) ==
  \A v \in Values : Count(s, i, v) = Count(t, i, v)

PartitionOK(s, t, i, p) ==
  /\ Len(t) = Len(s)
  /\ \A k \in 1..Len(s) :
        (k < i.low \/ k > i.high) => t[k] = s[k]
  /\ \A k \in i.low..p :
        \A l \in (p+1)..i.high : t[k] <= t[l]
  /\ PermPreserve(s, t, i)

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

(*-----------------------------------------------------------------
   Initialization
-----------------------------------------------------------------*)
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

(*-----------------------------------------------------------------
   Next-state relation
-----------------------------------------------------------------*)
Process ==
  /\ work # {}
  /\ \E i \in work :
        /\ IF IsSingleton(i) THEN
              /\ newSeq = seq
              /\ newWork = work \ {i}
           ELSE
              /\ \E p \in i.low..i.high :
                    /\ newSeq \in LimitedSeq(Values)
                    /\ PartitionOK(seq, newSeq, i, p)
                    /\ LET lower == [low |-> i.low, high |-> p-1] IN
                       LET upper == [low |-> p+1, high |-> i.high] IN
                         newWork = work \ {i}
                                   \cup (IF lower.low <= lower.high THEN {lower} ELSE {})
                                   \cup (IF upper.low <= upper.high THEN {upper} ELSE {})
        /\ seq' = newSeq
        /\ work' = newWork
        /\ pc' = "Loop"
        /\ UNCHANGED orig

Terminate ==
  /\ work = {}
  /\ pc = "Loop"
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

Stutter ==
  /\ pc = "Done"
  /\ work = {}
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ Process
  \/ Terminate
  \/ Stutter

(*-----------------------------------------------------------------
   Specification
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

(*-----------------------------------------------------------------
   Invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals(seq)
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ TypeOK
  /\ PermPreserve(orig, seq, [low |-> 1, high |-> Len(seq)])

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ PermPreserve(orig, seq, [low |-> 1, high |-> Len(seq)]))

(*-----------------------------------------------------------------
   Properties
-----------------------------------------------------------------*)
Termination ==
  <> (pc = "Done")

====