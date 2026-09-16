---- MODULE W4Od2m7p4t2 ----
EXTENDS Naturals
CONSTANTS Dispatchers, Cap
VARIABLES active, readSnapshots
vars == <<active, readSnapshots>>

Init == active = 0
\* Each dispatcher has read the initial active count
\* and has no stale snapshot
readSnapshots = [d \in Dispatchers |-> 0]

Next == \E d \in Dispatchers : (
    \E c \in 0..Cap : readSnapshots[d] = c
    /\ active < c
    /\ \A d' \in Dispatchers : d' # d
    => (active' = c + 1
        /\ readSnapshots' = [d' \in Dispatchers |-> IF d' = d THEN c + 1 ELSE readSnapshots[d'] END
                          \* Other dispatchers keep their stale snapshot
                          \* unless they have already read the new count
                          /\ \A d'' \in Dispatchers : d'' # d'
                          => readSnapshots''[d''] = readSnapshots''[d'']])
    \/ \E c \in 0.. Cap : readSnapshots[d] = active
    /\ active < c
        => (active' = active
            /\ readSnapshots' = [e \in Dispatchers |-> IF e = d THEN c
                                            ELSE readSnapshots[e] END]))

ActiveWithinCapacity == active # Cap
Spec == Init /\ [][Next]_vars
====