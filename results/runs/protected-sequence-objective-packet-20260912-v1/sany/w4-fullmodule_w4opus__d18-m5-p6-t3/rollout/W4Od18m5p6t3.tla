---- MODULE W4Od18m5p6t3 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Device, MaxEpoch

VARIABLES
  devices,  %% a set of devices in the network
  round,    %% the current round
  votes,    %% a set of votes for the current round
  clock,    %% a function mapping devices to their internal clock
  trust     %% a function mapping devices to their trust status

TypeOK ==
  /\ devices \subseteq Device
  /\ clock \in [Device -> 0..MaxEpoch]
  /\ trust \in [Device -> BOOLEAN]

Init ==
  /\ devices = {}
  /\ round = 0
  /\ votes = {}
  /\ clock = [d \in Device |-> 0]
  /\ trust = [d \in Device |-> TRUE]

Next ==
  \/ Vote(d)  %% a device casts a vote
    /\ devices = devices
    /\ round = round
    /\ clock = [d' \in Device | d' = d \/ d' \in devices \ {d} |-> clock[d']]
    /\ trust = [d' \in Device | d' = d \/ d' \in devices \ {d} |-> trust[d']]
    /\ votes = votes \cup {d}
    /\ UNCHANGED trust
  \/ CatchUp(d)  %% a device catches up
    /\ devices = devices
    /\ round = round
    /\ clock = [d' \in Device | d' = d \/ d' \in devices \ {d} |-> IF d' = d THEN clock[d] + 1 ELSE clock[d']]
    /\ trust = [d' \in Device | d' = d \/ d' \in devices \ {d} |-> trust[d']]
    /\ UNCHANGED trust
    /\ votes = votes
  \/ Unlock  %% a majority of devices have voted
    /\ devices = devices
    /\ round = round + 1
    /\ clock = [d \in Device |-> 0]
    /\ trust = [d \in Device |-> trust[d]]
    /\ votes = {}
  \/ Relock  %% the door is relocked
    /\ devices = devices
    /\ round = round
    /\ clock = [d \in Device |-> clock[d]]
    /\ trust = [d \in Device |-> trust[d]]
    /\ UNCHANGED trust
    /\ UNCHANGED votes
  \/ ToggleAuth(d, b)  %% a device's trust is toggled
    /\ devices = devices
    /\ round = round
    /\ clock = [d' \in Device | d' = d \/ d' \in devices \ {d} |-> clock[d']]
    /\ trust = [d' \in Device | d' = d \/ d' \in devices \ {d} |-> IF d' = d THEN b ELSE trust[d']]
    /\ UNCHANGED trust
    /\ UNCHANGED votes

Spec == Init /\ [][Next]_devices, round, clock, trust

VotesCoherent ==
  /\ votes \subseteq devices
  /\ \A d \in devices : (d \in votes) => trust[d] /\ clock[d] = round

====