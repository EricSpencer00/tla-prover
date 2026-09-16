---------------------------- MODULE W4Od0m2p0t1 ----------------------------
EXTENDS Naturals

CONSTANTS Teams, Rooms

None == "none"

VARIABLES
    pool,      \* unordered set of pending <<team, room>> prepare requests
    outbox,    \* unordered set of <<team, room>> lock-grant messages
    lockedBy,  \* lockedBy[r] = team granted room r's prepare lock, or None
    occupant   \* occupant[r] = team currently occupying room r, or None

vars == << pool, outbox, lockedBy, occupant >>

TypeOK ==
    /\ pool \subseteq (Teams \X Rooms)
    /\ outbox \subseteq (Teams \X Rooms)
    /\ lockedBy \in [Rooms -> Teams \cup {None}]
    /\ occupant \in [Rooms -> Teams \cup {None}]

Init ==
    /\ pool = {}
    /\ outbox = {}
    /\ lockedBy = [r \in Rooms |-> None]
    /\ occupant = [r \in Rooms |-> None]

\* A team drops a prepare request into the unordered request pool.
SendPrepare(t, r) ==
    /\ << t, r >> \notin pool
    /\ pool' = pool \cup {<< t, r >>}
    /\ UNCHANGED << outbox, lockedBy, occupant >>

\* The coordinator services any pending request for an unlocked room, granting it
\* the prepare lock and emitting a grant message.
Grant(t, r) ==
    /\ << t, r >> \in pool
    /\ lockedBy[r] = None
    /\ lockedBy' = [lockedBy EXCEPT ![r] = t]
    /\ pool' = pool \ {<< t, r >>}
    /\ outbox' = outbox \cup {<< t, r >>}
    /\ UNCHANGED occupant

\* A team consumes its grant message and occupies the room it was granted.
Commit(t, r) ==
    /\ << t, r >> \in outbox
    /\ lockedBy[r] = t
    /\ occupant[r] = None
    /\ occupant' = [occupant EXCEPT ![r] = t]
    /\ outbox' = outbox \ {<< t, r >>}
    /\ UNCHANGED << pool, lockedBy >>

\* An occupying team releases the room, dropping occupancy and freeing the lock.
Release(t, r) ==
    /\ occupant[r] = t
    /\ occupant' = [occupant EXCEPT ![r] = None]
    /\ lockedBy' = [lockedBy EXCEPT ![r] = None]
    /\ UNCHANGED << pool, outbox >>

Next ==
    \/ \E t \in Teams, r \in Rooms : SendPrepare(t, r)
    \/ \E t \in Teams, r \in Rooms : Grant(t, r)
    \/ \E t \in Teams, r \in Rooms : Commit(t, r)
    \/ \E t \in Teams, r \in Rooms : Release(t, r)

Spec == Init /\ [][Next]_vars

\* A team occupies a room only while holding that room's single prepare lock,
\* which forces mutual exclusion of every operating room.
LockedByHolder ==
    \A r \in Rooms : occupant[r] # None => lockedBy[r] = occupant[r]

=============================================================================