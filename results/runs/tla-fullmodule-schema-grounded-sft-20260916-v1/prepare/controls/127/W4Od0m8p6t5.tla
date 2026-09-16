------------------------- MODULE W4Od0m8p6t5 -------------------------
EXTENDS Naturals

CONSTANTS Surgeons, Rooms

FREE == "free"
ADMIN == "admin"
NONE == "none"

VARIABLES deptLock, roomLock, lastWriter, editing

vars == <<deptLock, roomLock, lastWriter, editing>>

TypeOK ==
  /\ deptLock \in Surgeons \cup {FREE}
  /\ roomLock \in [Rooms -> Surgeons \cup {FREE}]
  /\ lastWriter \in [Rooms -> Surgeons \cup {ADMIN, NONE}]
  /\ editing \subseteq Rooms

\* Any room with an edit in progress is held by a surgeon who owns BOTH the
\* coarse department lock and that room's fine lock: no stale or unauthorized
\* participant is ever mid-action.
Authorized ==
  \A r \in editing : roomLock[r] # FREE /\ deptLock = roomLock[r]

Init ==
  /\ deptLock = FREE
  /\ roomLock = [r \in Rooms |-> FREE]
  /\ lastWriter = [r \in Rooms |-> NONE]
  /\ editing = {}

GrabDept ==
  /\ deptLock = FREE
  /\ \E s \in Surgeons :
       deptLock' = s
  /\ UNCHANGED <<roomLock, lastWriter, editing>>

GrabRoom ==
  /\ \E s \in Surgeons, r \in Rooms :
       /\ deptLock = s
       /\ roomLock[r] = FREE
       /\ roomLock' = [roomLock EXCEPT ![r] = s]
  /\ UNCHANGED <<deptLock, lastWriter, editing>>

BeginEdit ==
  /\ \E s \in Surgeons, r \in Rooms :
       /\ deptLock = s
       /\ roomLock[r] = s
       /\ editing' = editing \cup {r}
  /\ UNCHANGED <<deptLock, roomLock, lastWriter>>

FinishEdit ==
  /\ \E r \in editing :
       /\ lastWriter' = [lastWriter EXCEPT ![r] = roomLock[r]]
       /\ editing' = editing \ {r}
  /\ UNCHANGED <<deptLock, roomLock>>

ReleaseRoom ==
  /\ \E s \in Surgeons, r \in Rooms :
       /\ roomLock[r] = s
       /\ r \notin editing
       /\ roomLock' = [roomLock EXCEPT ![r] = FREE]
  /\ UNCHANGED <<deptLock, lastWriter, editing>>

AdminRevoke ==
  /\ deptLock' = FREE
  /\ roomLock' = [r \in Rooms |-> FREE]
  /\ editing' = {}
  /\ UNCHANGED lastWriter

AdminForceWrite ==
  /\ \E r \in Rooms :
       lastWriter' = [lastWriter EXCEPT ![r] = ADMIN]
  /\ UNCHANGED <<deptLock, roomLock, editing>>

Next ==
  \/ GrabDept \/ GrabRoom \/ BeginEdit \/ FinishEdit
  \/ ReleaseRoom \/ AdminRevoke \/ AdminForceWrite

Spec == Init /\ [][Next]_vars

=============================================================================