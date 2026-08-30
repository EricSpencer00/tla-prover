---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, ZSequences

CONSTANTS CharacterSet

\* Nondeterministically choose any string over a finite alphabet of bounded length.
InputStrings == UNION { [1..n -> CharacterSet] : n \in 0..3 }

Variables == << str, strLen, fail, pIdx, loop, bestOff, pc >>

Sentinel == 99

TypeInvariant ==
    /\ str \in InputStrings
    /\ strLen = Len(str)
    /\ fail \in [0..2*strLen -> 0..strLen \cup {Sentinel}]
    /\ pIdx \in 0..strLen \cup {Sentinel}
    /\ loop \in 0..2*strLen
    /\ bestOff \in 0..(strLen - 1)
    /\ pc \in {"outerCheck", "failLookup", "compareLoop", "resetMatch", "postCompare", "increment", "done"}

Init ==
    /\ \E s \in InputStrings : str = s
    /\ strLen = Len(str)
    /\ fail = [i \in 0..2*strLen |-> Sentinel]
    /\ pIdx = Sentinel
    /\ loop = 1
    /\ bestOff = 0
    /\ pc = "outerCheck"

\* Outer loop: walk the string twice (to account for the wraparound) and compare
\* each rotation against the best one found so far.
OuterLoop ==
    /\ pc = "outerCheck"
    /\ IF loop < 2*strLen THEN pc' = "failLookup" ELSE pc' = "done"
    /\ UNCHANGED << str, strLen, fail, pIdx, loop, bestOff >>

FailLookup ==
    /\ pc = "failLookup"
    /\ fail' = [fail EXCEPT ![loop - bestOff] = fail[loop - bestOff]]
    /\ pIdx' = fail[loop - bestOff]
    /\ pc' = "compareLoop"
    /\ UNCHANGED << str, strLen, loop, bestOff >>

\* Inner loop: invariant: the fail-indexed prefix of the rotation at offset
\* 'loop' matches the prefix of the rotation at offset 'bestOff'.
CompareLoop ==
    /\ pc = "compareLoop"
    /\ IF pIdx # Sentinel /\ str[(loop % strLen) + 1] = str[(bestOff + pIdx) % strLen + 1]
         THEN pc' = "compareLoop"
         ELSE pc' = "postCompare"
    /\ UNCHANGED << str, strLen, fail, pIdx, loop, bestOff >>

\* If the current character is smaller than the candidate's, this rotation is
\* lexicographically better, so record its start offset.
UpdateIfBetter ==
    /\ pc = "compareLoop"
    /\ pIdx # Sentinel
    /\ str[(loop % strLen) + 1] < str[(bestOff + pIdx) % strLen + 1]
    /\ bestOff' = loop % strLen
    /\ UNCHANGED << str, strLen, fail, pIdx, loop, pc >>

FollowFailChain ==
    /\ pc = "compareLoop"
    /\ pIdx # Sentinel
    /\ pIdx' = fail[pIdx]
    /\ UNCHANGED << str, strLen, fail, loop, bestOff, pc >>

PostCompare ==
    /\ pc = "postCompare"
    /\ IF pIdx = Sentinel /\ str[(loop % strLen) + 1] < str[bestOff + 1]
         THEN bestOff' = loop % strLen
         ELSE bestOff' = bestOff
    /\ fail' = [fail EXCEPT ![loop - bestOff] = IF pIdx = Sentinel THEN Sentinel ELSE pIdx + 1]
    /\ pc' = "increment"
    /\ UNCHANGED << str, strLen, pIdx, loop >>

IncrementLoop ==
    /\ pc = "increment"
    /\ loop < 2*strLen
    /\ loop' = loop + 1
    /\ pIdx' = Sentinel
    /\ pc' = "outerCheck"
    /\ UNCHANGED << str, strLen, fail, bestOff >>

Done ==
    /\ pc = "done"
    /\ UNCHANGED Variables

\* Stutter in the final state so the model never deadlocks once the algorithm
\* has terminated.
Stutter ==
    /\ pc = "done"
    /\ UNCHANGED Variables

Next ==
    \/ OuterLoop
    \/ FailLookup
    \/ CompareLoop
    \/ UpdateIfBetter
    \/ FollowFailChain
    \/ PostCompare
    \/ IncrementLoop
    \/ Done
    \/ Stutter

Spec == Init /\ [][Next]_Variables

\* Correctness: the recorded rotation is not worse than any other rotation.
Correctness ==
    /\ (strLen = 0 => bestOff = 0)
    /\ (strLen > 0 =>
          \A i \in 0..(strLen - 1) :
            LET suffix(k) == SubSeq(str, k + 1, strLen) \inSeq [1..strLen -> CharacterSet]
                rot(k)    == suffix(k) \o suffix(0)
            IN rot(bestOff) <= rot(i))

\* Liveness: the algorithm eventually reaches its final state.
Termination == <>(pc = "done")

====