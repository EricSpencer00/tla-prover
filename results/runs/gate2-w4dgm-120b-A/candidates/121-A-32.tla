---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* A circular-string rotation algorithm from Booth's 1980 paper that builds a
   failure function in tandem with a nested loop, applied to every string over a
   bounded alphabet. The model checks the algorithm against all such strings up to
   a bounded length. *)
CONSTANTS CharacterSet, MaxLen, Undefined

VARIABLES string, length, failure, index, loop, bestOffset, pc

vars == <<string, length, failure, index, loop, bestOffset, pc>>

TypeInvariant ==
    /\ string \in Seq(CharacterSet)
    /\ length = Len(string)
    /\ length <= MaxLen
    /\ failure \in [0..(2 * MaxLen) -> 0..(2 * MaxLen) \cup {Undefined}]
    /\ index \in 0..(2 * MaxLen) \cup {Undefined}
    /\ loop \in 0..(2 * MaxLen)
    /\ bestOffset \in 0..MaxLen
    /\ pc \in {"outer", "lookup", "compare", "updateBest", "follow",
               "post", "done"}

Init ==
    /\ \E s \in Seq(CharacterSet) : string = s
    /\ length = Len(string)
    /\ failure = [i \in 0..(2 * MaxLen) |-> Undefined]
    /\ index = Undefined
    /\ loop = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ IF loop < 2 * length THEN pc' = "lookup" ELSE pc' = "done"
    /\ UNCHANGED <<string, length, failure, index, loop, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ index' = failure[loop - bestOffset]
    /\ pc' = "compare"
    /\ UNCHANGED <<string, length, failure, loop, bestOffset>>

CharAt(pos) == string[(pos % length) + 1]

Compare ==
    /\ pc = "compare"
    /\ IF CharAt(loop) # CharAt(loop - bestOffset) /\ index # Undefined
         THEN pc' = "updateBest"
         ELSE pc' = "post"
    /\ UNCHANGED <<string, length, failure, index, loop, bestOffset>>

UpdateBest ==
    /\ pc = "updateBest"
    /\ \* Update the running best rotation when the current character is strictly
       \* less than the candidate's comparison character.
    /\ IF CharAt(loop) < CharAt(loop - bestOffset)
         THEN bestOffset' = loop
         ELSE bestOffset' = bestOffset
    /\ index' = failure[index]
    /\ pc' = "compare"
    /\ UNCHANGED <<string, length, failure, loop>>

Post ==
    /\ pc = "post"
    /\ IF CharAt(loop) # CharAt(loop - bestOffset) /\ index = Undefined
         THEN bestOffset' = IF CharAt(loop) < CharAt(loop - bestOffset)
                             THEN loop ELSE bestOffset
         ELSE bestOffset' = bestOffset
    /\ failure' = [failure EXCEPT ![loop - bestOffset] =
                       IF index = Undefined THEN Undefined ELSE index + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<string, length, index, loop>>

Increment ==
    /\ pc = "increment"
    /\ loop' = loop + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<string, length, failure, index, bestOffset>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoop \/ Lookup \/ Compare \/ UpdateBest \/ Post \/ Increment \/ Done \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop)

Correctness ==
    /\ (pc = "done") => (bestOffset < length)
    /\ (pc = "done") => \A i \in 1..(length - 1) :
           \A k \in 1..length :
             (LET rot[j \in 1..length] ==
                   CharAt(j + i - 1)
              IN rot[i] < rot[1] \/ (rot[i] = rot[1] /\ i <= k))

Termination == (pc # "done") ~> (pc = "done")

====