---- MODULE W4Od17m1p0t3 ----
EXTENDS Naturals

CONSTANTS StationCount, BacklogBound, NoStation

Stations == 1..StationCount

\* The ring order: the permit always moves to the next station round.
NextRound(n) == IF n = StationCount THEN 1 ELSE n + 1

VARIABLES permitAt, onLink, feeding, onChute, waiting

vars == <<permitAt, onLink, feeding, onChute, waiting>>

TypeOK ==
    ( (permitAt \in Stations \cup {NoStation})
     /\  (onLink \in Stations \cup {NoStation})
     /\  (feeding \in [Stations -> BOOLEAN])
     /\  (onChute \in Stations \cup {NoStation})
     /\  (waiting \in [Stations -> 0..BacklogBound]))

Init ==
    ( (permitAt = 1)
     /\  (onLink = NoStation)
     /\  (feeding = [n \in Stations |-> FALSE])
     /\  (onChute = NoStation)
     /\  (waiting = [n \in Stations |-> 0]))

Arrive(n) ==
    ( (waiting[n] < BacklogBound)
     /\  (waiting' = [waiting EXCEPT ![n] = @ + 1])
     /\  (UNCHANGED <<permitAt, onLink, feeding, onChute>>))

\* Holding the permit is the only thing that lets a station onto the chute.
StartFeed(n) ==
    ( (permitAt = n)
     /\  (~feeding[n])
     /\  (waiting[n] > 0)
     /\  (feeding' = [feeding EXCEPT ![n] = TRUE])
     /\  (onChute' = n)
     /\  (UNCHANGED <<permitAt, onLink, waiting>>))

\* A slow station simply has more to work through; its backlog is bounded.
Feed(n) ==
    ( (feeding[n])
     /\  (waiting[n] > 0)
     /\  (waiting' = [waiting EXCEPT ![n] = @ - 1])
     /\  (UNCHANGED <<permitAt, onLink, feeding, onChute>>))

StopFeed(n) ==
    ( (feeding[n])
     /\  (feeding' = [feeding EXCEPT ![n] = FALSE])
     /\  (onChute' = NoStation)
     /\  (UNCHANGED <<permitAt, onLink, waiting>>))

\* The permit is only released once the station is off the chute.
Release(n) ==
    ( (permitAt = n)
     /\  (~feeding[n])
     /\  (permitAt' = NoStation)
     /\  (onLink' = NextRound(n))
     /\  (UNCHANGED <<feeding, onChute, waiting>>))

Deliver ==
    ( (onLink # NoStation)
     /\  (permitAt' = onLink)
     /\  (onLink' = NoStation)
     /\  (UNCHANGED <<feeding, onChute, waiting>>))

Next ==
    ( (Deliver)
     \/  (\E n \in Stations : Arrive(n) \/ StartFeed(n) \/ Feed(n) \/ StopFeed(n) \/ Release(n)))

Spec == Init /\ [][Next]_vars

\* The chute's record and the stations' own states never come apart.
ChuteRecordAgrees ==
    ( (\A n \in Stations : feeding[n] => onChute = n)
     /\  ((onChute # NoStation => feeding[onChute])))

====