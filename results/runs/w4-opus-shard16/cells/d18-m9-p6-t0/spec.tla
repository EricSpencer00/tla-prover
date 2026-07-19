-------------------------- MODULE W4Od18m9p6t0 --------------------------
EXTENDS Naturals

CONSTANTS Locks, NoLock, MaxEpoch

VARIABLES
    curEpoch,       \* hub's current epoch
    known,          \* known[l] : epoch each lock last learned
    crashed,        \* set of silently-crashed locks
    actedThisEpoch, \* has any lock acted under curEpoch?
    lastActor,      \* the lock that most recently acted, or NoLock
    lastEpoch       \* the epoch that most recent action was carried out under

vars == << curEpoch, known, crashed, actedThisEpoch, lastActor, lastEpoch >>

TypeOK ==
    /\ curEpoch \in 0..MaxEpoch
    /\ known \in [Locks -> 0..MaxEpoch]
    /\ crashed \subseteq Locks
    /\ actedThisEpoch \in BOOLEAN
    /\ lastActor \in (Locks \cup {NoLock})
    /\ lastEpoch \in 0..MaxEpoch

Init ==
    /\ curEpoch = 0
    /\ known = [l \in Locks |-> 0]
    /\ crashed = {}
    /\ actedThisEpoch = FALSE
    /\ lastActor = NoLock
    /\ lastEpoch = 0

\* The hub reconfigures, retiring the old epoch; no action yet under the new.
Reconfigure ==
    /\ curEpoch < MaxEpoch
    /\ curEpoch' = curEpoch + 1
    /\ actedThisEpoch' = FALSE
    /\ UNCHANGED << known, crashed, lastActor, lastEpoch >>

\* A lock catches up to the hub's current epoch.
Adopt(l) ==
    /\ l \notin crashed
    /\ known[l] < curEpoch
    /\ known' = [known EXCEPT ![l] = curEpoch]
    /\ UNCHANGED << curEpoch, crashed, actedThisEpoch, lastActor, lastEpoch >>

\* A current lock acts on the shared bolt, stamping the epoch it acted under.
Act(l) ==
    /\ l \notin crashed
    /\ known[l] = curEpoch
    /\ lastActor' = l
    /\ lastEpoch' = known[l]
    /\ actedThisEpoch' = TRUE
    /\ UNCHANGED << curEpoch, known, crashed >>

\* A lock crashes silently.
Crash(l) ==
    /\ l \notin crashed
    /\ crashed' = crashed \cup {l}
    /\ UNCHANGED << curEpoch, known, actedThisEpoch, lastActor, lastEpoch >>

\* A crashed lock recovers.
Recover(l) ==
    /\ l \in crashed
    /\ crashed' = crashed \ {l}
    /\ UNCHANGED << curEpoch, known, actedThisEpoch, lastActor, lastEpoch >>

Next ==
    \/ Reconfigure
    \/ \E l \in Locks : Adopt(l)
    \/ \E l \in Locks : Act(l)
    \/ \E l \in Locks : Crash(l)
    \/ \E l \in Locks : Recover(l)

Spec == Init /\ [][Next]_vars

\* No stale lock ever acts: any action recorded in the current epoch was in
\* fact carried out under the current epoch.
NoStaleAction == actedThisEpoch => (lastEpoch = curEpoch)

=============================================================================
