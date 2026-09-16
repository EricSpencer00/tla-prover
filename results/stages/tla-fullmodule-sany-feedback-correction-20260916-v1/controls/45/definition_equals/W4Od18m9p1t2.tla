---- MODULE W4Od18m9p1t2 ----
EXTENDS Naturals
Hubs = {"h1", "h2"}
Policies == {"day", "night"}
VARIABLES config, highWater
vars == <<config, highWater>>

Init ==
  /\ config = [policy |-> "day", epoch |-> 0]
  /\ highWater = 0

Reconfigure ==
  /\ config.epoch < 3
  /\ \E h \in Hubs, p \in Policies :
       /\ config' = [policy |-> p, epoch |-> config.epoch + 1]
  /\ highWater' = config.epoch + 1

HubHeartbeat ==
  /\ config' = config
  /\ highWater' = config.epoch

Next == Reconfigure \/ HubHeartbeat
Spec == Init /\ [][Next]_vars
NoStaleOverwrite == config.epoch >= highWater
====