---- MODULE W4Od14m4p0t4 ----
EXTENDS Integers, FiniteSets

CONSTANTS MaxQueue, NumDrones
ASSUME MaxQueue >= 0
ASSUME NumDrones >= 0
ASSUME MaxQueue >= NumDrones

VARIABLES
  queue,        /\ 0 <= queue <= MaxQueue
  downlink,     /\ downlink \in 0..NumDrones
  tasks,        /\ tasks \in 0..MaxQueue
  burst,        /\ burst \in 0..MaxQueue
  droneBurst,   /\ droneBurst \in 0..MaxQueue
  droneDownlink, /\ droneDownlink \in 0..NumDrones

TypeOK ==
  /\ queue \in 0..MaxQueue
  /\ tasks \in 0..MaxQueue
  /\ burst \in 0..MaxQueue
  /\ droneBurst \in 0..MaxQueue
  /\ droneDownlink \in 0..NumDrones
  /\ downlink \in 0..NumDrones

Init ==
  /\ TypeOK
  /\ queue = 0
  /\ tasks = 0
  /\ burst = 0
  /\ droneBurst = 0
  /\ droneDownlink = 0
  /\ downlink = 0

ExclusiveDownlink ==
  /\ downlink = 0
  \/ \A i \in 0..NumDrones : i # downlink => droneDownlink = i

Next ==
  /\ TypeOK
  /\ IF queue < MaxQueue
    THEN tasks' = tasks + 1
    ELSE tasks' = tasks
  /\ IF tasks > 0
    THEN downlink' = 0
    ELSE downlink' = downlink
  /\ IF downlink = 0
    THEN IF tasks > 0
      THEN burst' = 1
      ELSE burst' = 0
    ELSE burst' = 0
  /\ IF burst > 0
    THEN burst' = burst - 1
    ELSE burst' = 0
  /\ IF downlink # 0
    THEN IF burst > 0
      THEN droneBurst' = droneBurst + 1
      ELSE droneBurst' = 0
    ELSE droneBurst' = 0
  /\ IF droneBurst > 0
    THEN droneBurst' = droneBurst - 1
    ELSE droneBurst' = 0
  /\ IF downlink # 0
    THEN droneDownlink' = downlink
    ELSE droneDownlink' = 0
  /\ IF downlink # 0
    THEN downlink' = 0
    ELSE downlink' = downlink
  /\ IF downlink # 0
    THEN IF tasks > 0
      THEN queue' = queue + 1
      ELSE queue' = queue
    ELSE queue' = queue
  /\ IF queue > 0
    THEN tasks' = tasks - 1
    ELSE tasks' = tasks
  /\ droneDownlink' = 0
  /\ downlink' # droneDownlink'

Spec == Init /\ [][Next]_vars

====