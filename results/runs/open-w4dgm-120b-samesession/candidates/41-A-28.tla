---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* increment last-heard counters for all processes the local process has not
\* yet timed out on; this is capped by each process's own timeout interval.
AddForAllNotTimedOut(proc, s, lastHeard, timeout) ==
  UNION {
    {s[p] + 1} \ {s[p] + 1} \cup IF lastHeard[p] < timeout[p] THEN {s[p]} ELSE {}
      : p \in Proc : p # proc
  }

\* a process's own timeout interval may shrink back down during idle churn;
\* this is the only path that reduces a timeout interval.
DecayTimeouts(f) ==
  [p \in Proc |-> IF f[p] > 1 THEN f[p] - 1 ELSE f[p]]

VARIABLES suspicion, timeout, lastHeard, localTime, outbound

vars == <<suspicion, timeout, lastHeard, localTime, outbound>>

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ outbound \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [proc \in Proc |-> {}]
  /\ timeout = [proc \in Proc |-> [p \in Proc |-> d0]]
  /\ lastHeard = [proc \in Proc |-> [p \in Proc |-> 0]]
  /\ localTime = [proc \in Proc |-> 0]
  /\ outbound = [proc \in Proc |-> {}]

SendAlive ==
  /\ \E proc \in Proc:
       /\ (localTime[proc] % SendPoint = 0) /\ (localTime[proc] % PredictPoint # 0)
       /\ outbound' = [outbound EXCEPT ![proc] =
            outbound[proc] \cup { [from |-> proc, to |-> p] : p \in Proc : p # proc }]
       /\ localTime' = [localTime EXCEPT ![proc] = @ + 1]
       /\ lastHeard' = [lastHeard EXCEPT ![proc] = AddForAllNotTimedOut(proc,
            lastHeard[proc], timeout[proc])]
  /\ UNCHANGED <<suspicion, timeout>>

MakePrediction ==
  /\ \E proc \in Proc:
       /\ (localTime[proc] % PredictPoint = 0) /\ (localTime[proc] % SendPoint # 0)
       /\ suspicion' = [suspicion EXCEPT ![proc] =
            @ \cup
              {p \in Proc :
                 /\ p # proc
                 /\ lastHeard[proc][p] >= timeout[proc][p]}
          ]
       /\ localTime' = [localTime EXCEPT ![proc] = @ + 1]
       /\ lastHeard' = [lastHeard EXCEPT ![proc] = AddForAllNotTimedOut(proc,
            lastHeard[proc], timeout[proc])]
  /\ UNCHANGED <<timeout, outbound>>

ReceiveMessages ==
  /\ \E proc \in Proc:
       /\ (localTime[proc] % SendPoint # 0) /\ (localTime[proc] % PredictPoint # 0)
       /\ LET done == {m \in outbound[proc] : m.to = proc}
              timeoutUpdates == [p \in Proc |-> IF p \in done THEN timeout[proc][p] + 1 ELSE timeout[proc][p]]
          IN /\ suspicion' = [suspicion EXCEPT ![proc] = @ \ {p \in Proc : [from |-> p, to |-> proc] \in done}]
             /\ timeout' = [timeout EXCEPT ![proc] = timeoutUpdates]
             /\ lastHeard' = [lastHeard EXCEPT ![proc] =
                  [p \in Proc |->
                     IF p \in done THEN 0
                     ELSE IF lastHeard[proc][p] < timeoutUpdates[p] THEN lastHeard[proc][p]
                     ELSE timeoutUpdates[p]]]
       /\ outbound' = [outbound EXCEPT ![proc] = {}]
       /\ localTime' = [localTime EXCEPT ![proc] = IF localTime[proc] >= SendPoint /\ localTime[proc] >= PredictPoint
                                                    /\ \A p \in Proc : localTime[proc] >= timeout[proc][p]
                                                    THEN 0 ELSE localTime[proc] + 1]

Next == SendAlive \/ MakePrediction \/ ReceiveMessages

Spec == Init /\ [][Next]_vars

====