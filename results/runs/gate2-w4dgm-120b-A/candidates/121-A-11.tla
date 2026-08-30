---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\* Zero-indexed sequences; the circular string is handled by indexing
\* modulo the string length as the algorithm iterates twice over it.
\* The model checker nondeterministically chooses the input string, so
\* correctness is verified for every string in the bounded corpus.

CONSTANTS CharacterSet

Sentinel == "sentinel"
MaxString == 4

VARIABLES string, len, fail, patIdx, outer, best, pc

vars == <<string, len, fail, patIdx, outer, best, pc>>

MaxP(i) == IF i < len THEN i ELSE i - len

TypeInvariant ==
  /\ string \in Seq(CharacterSet)
  /\ Len(string) <= MaxString
  /\ len = Len(string)
  /\ fail \in [0..(2 * MaxString) -> (0..(2 * MaxString)) \cup {Sentinel}]
  /\ patIdx \in (0..(2 * MaxString)) \cup {Sentinel}
  /\ outer \in 0..(2 * MaxString)
  /\ best \in 0..(MaxString - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "compareLess",
              "followChain", "postComp", "increment", "terminated"}

Init ==
  /\ \E s \in Seq(CharacterSet) : string = s
  /\ len = Len(string)
  /\ fail = [i \in 0..(2 * MaxString) |-> Sentinel]
  /\ patIdx = Sentinel
  /\ outer = 1
  /\ best = 0
  /\ pc = "outerCheck"

OuterLoop ==
  /\ pc = "outerCheck"
  /\ outer < (2 * len)
  /\ pc' = "lookup"
  /\ UNCHANGED <<string, len, fail, patIdx, outer, best>>

Lookup ==
  /\ pc = "lookup"
  /\ fail' = [fail EXCEPT ![outer] = fail[MaxP(outer)]]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<string, len, patIdx, outer, best>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ (string[MaxP(outer)] # string[MaxP(best + outer)]
        /\ patIdx # Sentinel)
  /\ pc' = "compareLess"
  /\ UNCHANGED <<string, len, fail, patIdx, outer, best>>

CompareLess ==
  /\ pc = "compareLess"
  /\ (string[MaxP(outer)] < string[MaxP(best + outer)]
        /\ best' = MaxP(outer)
        /\ patIdx' = fail[MaxP(outer)])
  /\ pc' = "followChain"
  /\ UNCHANGED <<string, len, fail, outer>>

FollowChain ==
  /\ pc = "followChain"
  /\ fail' = [fail EXCEPT ![MaxP(outer)] = patIdx]
  /\ pc' = "increment"
  /\ UNCHANGED <<string, len, patIdx, outer, best>>

PostComp ==
  /\ pc = "postComp"
  /\ (string[MaxP(outer)] # string[MaxP(best + outer)]
        /\ patIdx = Sentinel)
  /\ IF string[MaxP(outer)] < string[MaxP(best + outer)]
        THEN best' = MaxP(outer) ELSE best' = best
  /\ fail' = IF string[MaxP(outer)] = string[MaxP(best + outer)]
        THEN fail
        ELSE [fail EXCEPT ![MaxP(outer)] = IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<string, len, patIdx, outer>>

Increment ==
  /\ pc = "increment"
  /\ outer' = outer + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<string, len, fail, patIdx, best>>

Terminate ==
  /\ pc = "outerCheck"
  /\ outer >= (2 * len)
  /\ pc' = "terminated"
  /\ UNCHANGED <<string, len, fail, patIdx, outer, best>>

Stutter ==
  /\ pc = "terminated"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ Lookup \/ InnerLoop \/ CompareLess \/ FollowChain
  \/ PostComp \/ Increment \/ Terminate \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Terminate)

Correctness ==
  /\ \A o \in 0..(len - 1) : Len(string) > 0
        => string[best..(len - 1)] ^ string[0..(best - 1)]
           <= string[o..(len - 1)] ^ string[0..(o - 1)]
  /\ \A o \in 0..(len - 1) :
        (string[best..(len - 1)] ^ string[0..(best - 1)]
           = string[o..(len - 1)] ^ string[0..(o - 1)])
           => best <= o

Termination == WF_vars(Terminate)
====