---- MODULE W4Od4m0p4t3 ----
EXTENDS Naturals

CONSTANTS Attendants, LineCap, MaxVersion

NoSnap == MaxVersion + 1

VARIABLES version, onLine, cleared, snapVer, snapOcc

vars == <<version, onLine, cleared, snapVer, snapOcc>>

\* Everything that has been committed against the line's capacity: vehicles already
\* on it, plus vehicles cleared onto the ramp that are still to roll on.
Committed == onLine + cleared

TypeOK ==
  ( (version \in 0..MaxVersion)
   /\  (onLine \in 0..LineCap)
   /\  (cleared \in 0..LineCap)
   /\  (snapVer \in [Attendants -> 0..(MaxVersion + 1)])
   /\  (snapOcc \in [Attendants -> 0..LineCap]))

Init ==
  ( (version = 0)
   /\  (onLine = 0)
   /\  (cleared = 0)
   /\  (snapVer = [a \in Attendants |-> NoSnap])
   /\  (snapOcc = [a \in Attendants |-> 0]))

TakeSnapshot(a) ==
  ( (snapVer[a] = NoSnap)
   /\  (snapVer' = [snapVer EXCEPT ![a] = version])
   /\  (snapOcc' = [snapOcc EXCEPT ![a] = Committed])
   /\  (UNCHANGED <<version, onLine, cleared>>))

\* The attendant acts on the occupancy it read, not on a fresh reading; the version
\* match is what certifies that the old reading is still the truth.
CommitClear(a) ==
  ( (snapVer[a] # NoSnap)
   /\  (snapVer[a] = version)
   /\  (version < MaxVersion)
   /\  (snapOcc[a] + 1 <= LineCap)
   /\  (cleared' = cleared + 1)
   /\  (version' = version + 1)
   /\  (snapVer' = [snapVer EXCEPT ![a] = NoSnap])
   /\  (UNCHANGED <<onLine, snapOcc>>))

Retry(a) ==
  ( (snapVer[a] # NoSnap)
   /\  ((snapVer[a] # version \/ snapOcc[a] + 1 > LineCap \/ version = MaxVersion))
   /\  (snapVer' = [snapVer EXCEPT ![a] = NoSnap])
   /\  (UNCHANGED <<version, onLine, cleared, snapOcc>>))

RollOn ==
  ( (cleared > 0)
   /\  (version < MaxVersion)
   /\  (cleared' = cleared - 1)
   /\  (onLine' = onLine + 1)
   /\  (version' = version + 1)
   /\  (UNCHANGED <<snapVer, snapOcc>>))

Exit ==
  ( (onLine > 0)
   /\  (version < MaxVersion)
   /\  (onLine' = onLine - 1)
   /\  (version' = version + 1)
   /\  (UNCHANGED <<cleared, snapVer, snapOcc>>))

Next ==
  ( (\E a \in Attendants : TakeSnapshot(a) \/ CommitClear(a) \/ Retry(a))
   \/  (RollOn)
   \/  (Exit))

Spec ==
  ( (Init)
   /\  ([][Next]_vars)
   /\  (\A a \in Attendants : WF_vars(CommitClear(a) \/ Retry(a))))

LineNotOverfilled == Committed <= LineCap

\* A slow attendant still always gets its snapshot resolved one way or the other.
SnapshotsResolve ==
  \A a \in Attendants : (snapVer[a] # NoSnap) ~> (snapVer[a] = NoSnap)

====