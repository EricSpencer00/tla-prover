---- MODULE W4Od13m4p0t3 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Dispenser, Workers, MaxQueue
ASSUME MaxQueue >= 0
ASSUME Dispenser \in Workers

VARIABLES
  queue,  %% the bounded work queue
  dispenser,  %% the dispenser lock
  job,  %% the current job being processed
  worker,  %% the worker currently holding the dispenser lock
  idle  %% a set of idle workers

TypeOK ==
  queue \in [0, MaxQueue] \cup {MaxQueue + 1}
  dispenser \in Workers
  job \in Workers \cup {NONE}
  worker \in Workers
  idle \subseteq Workers

Init ==
  queue = 0
  dispenser = Dispenser
  job = NONE
  worker = Dispenser
  idle = Workers \ {Dispenser}

Next ==
  /\ queue < MaxQueue
  /\ (job = NONE \/ /\ job \in Workers /\ worker = job)
  /\ (dispenser = worker \/ /\ dispenser \in Workers /\ worker \notin idle)
  /\ (idle = Workers \ {dispenser} \/ /\ idle = Workers \ {dispenser, job})

Spec == Init /\ [][Next]_<<queue, dispenser, job, worker, idle>>

MutualExclusion ==
  (worker = Dispenser) => (dispenser = Dispenser)

====