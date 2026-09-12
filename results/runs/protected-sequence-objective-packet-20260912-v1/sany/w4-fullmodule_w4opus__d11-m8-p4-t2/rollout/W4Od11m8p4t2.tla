---- MODULE W4Od11m8p4t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Jobs, Instances, Cap, NULL

VARIABLES
  printerGroupLocks,
  jobFineLocks,
  waitingSet,
  spooledJobs,
  spoolerCapacity,
  spoolerInstanceLocks

vars == <<printerGroupLocks, jobFineLocks, waitingSet, spooledJobs, spoolerCapacity, spoolerInstanceLocks>>

TypeOK ==
  /\ printerGroupLocks \in [Instances -> 1..1]
  /\ jobFineLocks \in [Jobs -> 1..1]
  /\ waitingSet \subseteq Jobs
  /\ spooledJobs \subseteq Jobs
  /\ spoolerCapacity \in 1..Cap
  /\ spoolerInstanceLocks \in [Instances -> 1..1]

Init ==
  /\ printerGroupLocks = [i \in Instances |-> 0]
  /\ jobFineLocks = [j \in Jobs |-> 0]
  /\ waitingSet = {}
  /\ spooledJobs = {}
  /\ spoolerCapacity = 0
  /\ spoolerInstanceLocks = [i \in Instances |-> 0]
  /\ TypeOK

Next ==
  /\ \A i \in Instances, g \in Instances : printerGroupLocks' = [k \in Instances |-> IF k = g THEN 1 ELSE printerGroupLocks[k]]
  /\ \A i \in Instances, g \in Instances, j \in Jobs : (jobFineLocks' = [k \in Jobs |-> IF k = j THEN 1 + printerGroupLocks[i] ELSE jobFineLocks[k]])
  /\ \A i \in Instances : (spoolerInstanceLocks' = [k \in Instances |-> IF k = i THEN 1 + printerGroupLocks[i] + jobFineLocks[waitingSet[i]] ELSE spoolerInstanceLocks[k]))
  /\ \A g \in Instances : waitingSet' = [i \in Instances |-> IF i = g THEN waitingSet \ {waitingSet[g]} ELSE waitingSet[i]]
  /\ \A g \in Instances : spooledJobs' = [i \in Instances |-> IF i = g /\ spoolerInstanceLocks[i] > 1 /\ #spooledJobs < spoolerCapacity THEN spooledJobs \cup {waitingSet[g]} ELSE spooledJobs[i]]
  /\ TypeOK

Spec == Init /\ [][Next]_vars

BoundedCapacity == \A g \in Instances : #spooledJobs \subseteq g < spoolerCapacity

====