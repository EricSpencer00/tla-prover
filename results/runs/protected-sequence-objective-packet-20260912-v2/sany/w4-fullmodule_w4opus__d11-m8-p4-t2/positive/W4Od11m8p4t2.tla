--------------------------- MODULE W4Od11m8p4t2 ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Jobs, Instances, Cap, NULL

Groups == {1, 2}
GroupOf(j) == IF j = 1 THEN 1 ELSE 2

VARIABLES
    groupLock,  \* groupLock[g]: instance holding printer-group g's coarse lock
    jobLock,    \* jobLock[j]: instance holding job j's fine lock, or NULL
    spooled,    \* jobs currently spooled to printers
    queued      \* jobs waiting to be spooled

vars == <<groupLock, jobLock, spooled, queued>>

TypeOK ==
    /\ groupLock \in [Groups -> Instances \cup {NULL}]
    /\ jobLock \in [Jobs -> Instances \cup {NULL}]
    /\ spooled \subseteq Jobs
    /\ queued \subseteq Jobs

Init ==
    /\ groupLock = [g \in Groups |-> NULL]
    /\ jobLock = [j \in Jobs |-> NULL]
    /\ spooled = {}
    /\ queued = {}

Submit(j) ==
    /\ j \notin queued
    /\ j \notin spooled
    /\ queued' = queued \cup {j}
    /\ UNCHANGED <<groupLock, jobLock, spooled>>

\* Take the coarse printer-group lock first.
LockGroup(i, g) ==
    /\ groupLock[g] = NULL
    /\ groupLock' = [groupLock EXCEPT ![g] = i]
    /\ UNCHANGED <<jobLock, spooled, queued>>

\* Only under the group lock may an instance take a job's fine lock.
LockJob(i, j) ==
    /\ groupLock[GroupOf(j)] = i
    /\ jobLock[j] = NULL
    /\ jobLock' = [jobLock EXCEPT ![j] = i]
    /\ UNCHANGED <<groupLock, spooled, queued>>

\* Spool a queued job while holding both locks, only if capacity allows.
Spool(i, j) ==
    /\ jobLock[j] = i
    /\ groupLock[GroupOf(j)] = i
    /\ j \in queued
    /\ j \notin spooled
    /\ Cardinality(spooled) < Cap
    /\ spooled' = spooled \cup {j}
    /\ queued' = queued \ {j}
    /\ UNCHANGED <<groupLock, jobLock>>

UnlockJob(i, j) ==
    /\ jobLock[j] = i
    /\ jobLock' = [jobLock EXCEPT ![j] = NULL]
    /\ UNCHANGED <<groupLock, spooled, queued>>

UnlockGroup(i, g) ==
    /\ groupLock[g] = i
    /\ groupLock' = [groupLock EXCEPT ![g] = NULL]
    /\ UNCHANGED <<jobLock, spooled, queued>>

Complete(j) ==
    /\ j \in spooled
    /\ spooled' = spooled \ {j}
    /\ UNCHANGED <<groupLock, jobLock, queued>>

Next ==
    \/ \E j \in Jobs : Submit(j) \/ Complete(j)
    \/ \E i \in Instances, g \in Groups : LockGroup(i, g) \/ UnlockGroup(i, g)
    \/ \E i \in Instances, j \in Jobs : LockJob(i, j) \/ Spool(i, j) \/ UnlockJob(i, j)

Spec == Init /\ [][Next]_vars

\* Bounded capacity is never exceeded: the number of jobs concurrently spooled
\* to printers never exceeds the spooler's capacity.
BoundedCapacity ==
    Cardinality(spooled) <= Cap

=========================================================================