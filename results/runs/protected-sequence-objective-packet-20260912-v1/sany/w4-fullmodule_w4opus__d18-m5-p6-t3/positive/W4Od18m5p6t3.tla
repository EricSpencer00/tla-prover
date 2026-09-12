------------------------------ MODULE W4Od18m5p6t3 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Device, MaxEpoch

VARIABLES authorized, devEpoch, epoch, votes, doorState

TypeOK ==
  /\ authorized \in [Device -> BOOLEAN]
  /\ devEpoch \in [Device -> 0..MaxEpoch]
  /\ epoch \in 0..MaxEpoch
  /\ votes \subseteq Device
  /\ doorState \in {"locked", "unlocked"}

Init ==
  /\ authorized = [d \in Device |-> TRUE]
  /\ devEpoch = [d \in Device |-> 0]
  /\ epoch = 0
  /\ votes = {}
  /\ doorState = "locked"

\* Vote: a device may only cast a vote in the current round if it is a
\* trusted member of the network and its own clock is not lagging behind.
Vote(d) ==
  /\ authorized[d]
  /\ devEpoch[d] = epoch
  /\ d \notin votes
  /\ votes' = votes \cup {d}
  /\ UNCHANGED <<authorized, devEpoch, epoch, doorState>>

\* CatchUp: a slow device (one that has not failed, just lagged) advances
\* its own clock to the network's current round so it can vote again.
CatchUp(d) ==
  /\ devEpoch[d] < epoch
  /\ devEpoch' = [devEpoch EXCEPT ![d] = epoch]
  /\ UNCHANGED <<authorized, epoch, votes, doorState>>

\* Unlock: once a strict quorum majority of the network has voted in the
\* current round, the door opens and a fresh voting round begins.
Unlock ==
  /\ doorState = "locked"
  /\ epoch < MaxEpoch
  /\ 2 * Cardinality(votes) > Cardinality(Device)
  /\ doorState' = "unlocked"
  /\ epoch' = epoch + 1
  /\ votes' = {}
  /\ UNCHANGED <<authorized, devEpoch>>

\* Relock: the door can always be manually relocked, independent of the
\* voting round, so the network never stalls once the door is open.
Relock ==
  /\ doorState = "unlocked"
  /\ doorState' = "locked"
  /\ UNCHANGED <<authorized, devEpoch, epoch, votes>>

\* ToggleAuth: the network's admin adds or removes a device's trust. Losing
\* trust immediately strikes any vote that device already cast this round.
ToggleAuth(d) ==
  /\ authorized' = [authorized EXCEPT ![d] = ~@]
  /\ votes' = IF authorized[d] THEN votes \ {d} ELSE votes
  /\ UNCHANGED <<devEpoch, epoch, doorState>>

Next ==
  \E d \in Device :
    \/ Vote(d)
    \/ CatchUp(d)
    \/ Unlock
    \/ Relock
    \/ ToggleAuth(d)

vars == <<authorized, devEpoch, epoch, votes, doorState>>

Spec == Init /\ [][Next]_vars

\* Safety: every vote counted toward a quorum in the current round belongs
\* to a device that is both currently trusted and not lagging behind.
VotesCoherent ==
  votes \subseteq {d \in Device : authorized[d] /\ devEpoch[d] = epoch}

=============================================================================