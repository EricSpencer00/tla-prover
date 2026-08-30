---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* The character set is a constant, but it is redefined as the finite   *)
(* subset of Nat named CharacterSet in the .cfg, so Nat stays available. *)
CONSTANTS CharacterSet

(* The input is a zero-indexed string drawn nondeterministically from all *)
(* zero-indexed strings over the character set.  The failure function is   *)
(* modeled as an array of integer entries, each pointing to a previous     *)
(* position or to the sentinel value -1.                                   *)

Sentinel == -1

VARIABLES inputString, n, failFunc, patternIndex, k, bestOffset, pc

vars == <<inputString, n, failFunc, patternIndex, k, bestOffset, pc>>

TypeInvariant ==
    /\ inputString \in [1..n -> CharacterSet]
    /\ n \in Nat
    /\ failFunc \in [0..2*n -> (0..2*n) \cup {Sentinel}]
    /\ patternIndex \in (0..2*n) \cup {Sentinel}
    /\ k \in 1..(2*n)
    /\ bestOffset \in 0..(n - 1)
    /\ pc \in {"outerCheck", "lookup", "compare", "compareLess",
               "followChain", "postCompare", "increment", "done"}

Init ==
    /\ \E s \in Seq(CharacterSet) : inputString = s
    /\ n = Len(inputString)
    /\ failFunc = [i \in 0..(2*n) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ k = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ pc' = IF k < 2 * n THEN "lookup" ELSE "done"
    /\ UNCHANGED <<inputString, n, failFunc, patternIndex, k, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ patternIndex' = failFunc[bestOffset + k]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, n, failFunc, k, bestOffset>>

CharAt(i) == inputString[(i % n) + 1]

Compare ==
    /\ pc = "compare"
    /\ CharAt(k) # CharAt(bestOffset + k)
    /\ patternIndex # Sentinel
    /\ pc' = "compareLess"
    /\ UNCHANGED <<inputString, n, failFunc, patternIndex, k, bestOffset>>

CompareLess ==
    /\ pc = "compareLess"
    /\ IF CharAt(k) < CharAt(bestOffset + k)
       THEN bestOffset' = k
       ELSE bestOffset' = bestOffset
    /\ pc' = "followChain"
    /\ UNCHANGED <<inputString, n, failFunc, patternIndex, k>>

FollowChain ==
    /\ pc = "followChain"
    /\ patternIndex' = failFunc[patternIndex]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, n, failFunc, k, bestOffset>>

PostCompare ==
    /\ pc = "compare"
    /\ CharAt(k) # CharAt(bestOffset + k)
    /\ patternIndex = Sentinel
    /\ bestOffset' = IF CharAt(k) < CharAt(bestOffset + k) THEN k ELSE bestOffset
    /\ failFunc' = [failFunc EXCEPT
                       ![bestOffset + k] = IF patternIndex = Sentinel
                                            THEN Sentinel
                                            ELSE patternIndex + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, n, patternIndex, k>>

Increment ==
    /\ pc = "increment"
    /\ k' = k + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, n, failFunc, patternIndex, bestOffset>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ Compare \/ CompareLess \/ FollowChain
    \/ PostCompare \/ Increment \/ Done \/ Stutter

Spec == Init /\ [][Next]_vars

(* A rotation is identified by its start offset plus one, because a zero-  *)
(* length string has no characters; the offset must be zero for that case. *)
Substring(offset) == SelectSeq(inputString, 1, n, (i) |-> offset + i)

Correctness ==
    /\ \A i \in 0..(n - 1) : Substring(bestOffset) =< Substring(i)
    /\ \A i \in 0..(n - 1) : Substring(bestOffset) = Substring(i) => bestOffset <= i

Termination == <>(pc = "done")

====