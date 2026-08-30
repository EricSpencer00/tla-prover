---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    CharacterSet

\* The model inherits Nat from Naturals; the .cfg file replaces it with a
\* finite subset (the bounded character set) so the model stays checkable.
\* Do NOT redeclare Nat here -- keep EXTENDS Naturals and obey the .cfg.
\* The Alphabet set is a view of the constant as a finite set.
Alphabet == CharacterSet

\* Input is a zero-indexed sequence over a bounded alphabet.
\* The failure function is an array indexed over the doubled string.
\* The algorithm tracks its position with a loop counter and a program
\* counter naming the current labeled step; the stutter action keeps the
\* model from deadlocking once the algorithm has terminated.
VARIABLES
    inputString, length, failarray, pattern, loop, best, pc

vars == << inputString, length, failarray, pattern, loop, best, pc >>

Sentinel == 0
MaxLoop == 4
MaxLength == 2

TypeInvariant ==
    /\ inputString \in Seq(Alphabet)
    /\ length = Len(inputString)
    /\ failarray \in [0..(2 * MaxLength) -> 0..(MaxLength + 1)]
    /\ pattern \in 0..(MaxLength + 1)
    /\ loop \in 0..MaxLoop
    /\ best \in 0..MaxLength
    /\ pc \in [node : {"outer", "faillookup", "compare", "update", "followup"},
               pos : 0..MaxLoop]

\* The body of the outer loop; the loop counter bounds the number of
\* iterations and the inner compare loop is bounded by the failure chain.
Init ==
    /\ \E s \in Seq(Alphabet) :
        /\ inputString = s
        /\ length = Len(s)
    /\ failarray = [i \in 0..(2 * MaxLength) |-> Sentinel]
    /\ pattern = Sentinel
    /\ loop = 1
    /\ best = 0
    /\ pc = [node |-> "outer", pos |-> 0]

OuterCheck ==
    /\ pc' = IF pc.node = "outer" THEN
                 IF loop < MaxLoop
                 THEN [node |-> "faillookup", pos |-> loop]
                 ELSE [node |-> "done", pos |-> pc.pos]
              ELSE pc
    /\ UNCHANGED << inputString, length, failarray, pattern, loop, best >>

\* The failure function is probed before the inner compare, so the
\* pattern-matching index is set from the array before it is used.
FailLookup ==
    /\ pc.node = "faillookup"
    /\ pattern' = failarray[pc.pos]
    /\ pc' = [node |-> "compare", pos |-> pc.pos]
    /\ UNCHANGED << inputString, length, failarray, loop, best >>

\* The inner loop: compare the current rotation character with the
\* candidate character. The sentinel guards the loop-chain exit.
Compare ==
    /\ pc.node = "compare"
    /\ /\ IF pattern = Sentinel
       THEN NOT (inputString[(pc.pos + (best + pattern) % length) % length]
                 = inputString[(pc.pos + best) % length])
       ELSE inputString[(pc.pos + (best + pattern) % length) % length]
            <= inputString[(pc.pos + best) % length]
    /\ pc' = [node |-> IF pattern = Sentinel
                       THEN "followup"
                       ELSE "update",
               pos |-> pc.pos]
    /\ UNCHANGED << inputString, length, failarray, pattern, loop, best >>

\* Updating the best offset on the interior of the compare chain.
Update ==
    /\ pc.node = "update"
    /\ inputString[(pc.pos + (best + pattern) % length) % length]
         < inputString[(pc.pos + best) % length]
    /\ best' = (best + pattern) % length
    /\ UNCHANGED << inputString, length, failarray, pattern, loop, pc >>

\* Follow the failure chain to a shorter border, or break out once
\* the sentinel is reached and the candidate is not better.
Followup ==
    /\ pc.node = "followup"
    /\ IF inputString[(pc.pos + (best + pattern) % length) % length]
            < inputString[(pc.pos + best) % length]
       THEN best' = (best + pattern) % length
       ELSE best' = best
    /\ failarray' = [failarray EXCEPT ![pc.pos] = IF pattern = Sentinel
                                                THEN Sentinel
                                                ELSE pattern + 1]
    /\ pattern' = IF pattern = Sentinel THEN Sentinel ELSE pattern + 1
    /\ pc' = [node |-> "outer", pos |-> pc.pos]
    /\ UNCHANGED << inputString, length, loop >>

Next == OuterCheck \/ FailLookup \/ Compare \/ Update \/ Followup

\* When the loop has exhausted twice the string, the algorithm quiesces
\* in its final state rather than deadlocking the state graph.
Stutter ==
    /\ pc.node = "done"
    /\ UNCHANGED vars

\* A loop counter that moves on its own bound makes progress independent
\* of the compare chain, so weak fairness on the outer check is enough.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ [][Stutter]_vars
    /\ WF_vars(OuterCheck)

\* The chosen rotation is no worse than any other, and a rotation that
\* ties on the string value but starts earlier is never left as best.
Correctness ==
    /\ \A i \in 0..(length - 1) :
         RotateSeq(inputString, best) <= RotateSeq(inputString, i)
    /\ \A i \in 0..(length - 1) :
         RotateSeq(inputString, best) = RotateSeq(inputString, i) => best <= i

\* The bounded outer loop is guaranteed to run down to termination.
Termination == <>(pc.node = "done")

\* The configuration file sets the FINITE bound on the character set.
====