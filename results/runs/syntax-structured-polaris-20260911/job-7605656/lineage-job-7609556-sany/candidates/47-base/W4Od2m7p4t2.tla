---- MODULE W4Od2m7p4t2 ----

CONSTANTS Dispatchers, Cap

VARIABLES
  activeCount,
  readSnapshots

Init == activeCount = 0
  /\ readSnapshots = <<>>: Dispatchers -> Nat

Next == IF activeCount < Cap
  THEN activeCount' = activeCount + 1
  /\ readSnapshots' = readSnapshots
  /\ IF activeCount' = activeCount + 1
    THEN readSnapshots' = [d \in Dispatchers |-> activeCount]
    ELSE readSnapshots' = readSnapshots
  ELSE
    readSnapshots' = readSnapshots
  /\ activeCount' = activeCount

ActiveWithinCapacity == activeCount <= Cap

SPECIFICATION
  Init /\ [Next]^* /\ ActiveWithinCapacity

====