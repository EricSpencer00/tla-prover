---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* An eventually perfect failure detector: correct processes periodically
\* broadcast alive messages and predict crashes on timeouts; predictions
\* are always eventually cleared once the crashed process is heard from.
VARIABLES clock, timeout, lastHeard, suspect, pending

Message == [from: Proc, to: Proc]

TypeOK ==
  /\ clock \in [Proc -> 0 .. PredictPoint]
  /\ timeout \in [Proc -> [Proc -> 1 .. PredictPoint]]
  /\ lastHeard \in [Proc -> [Proc -> 0 .. PredictPoint]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ pending \in [Proc -> SUBSET Message]

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ suspect = [p \in Proc |-> {}]
  /\ pending = [p \in Proc |-> {}]

\* Send alive messages at multiples of SendPoint, but never at a PredictPoint.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ pending' = [pending EXCEPT ![p] =
        { [from |-> p, to |-> q] : q \in Proc }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT
        ![p] = [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q]
                                 THEN lastHeard[p][q] + 1 ELSE timeout[p][q]]]
  /\ UNCHANGED <<timeout, suspect>>

\* Predict crashes on timeouts at multiples of PredictPoint, not SendPoint.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
        { q \in Proc : lastHeard[p][q] > timeout[p][q] }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT
        ![p] = [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q]
                                 THEN lastHeard[p][q] + 1 ELSE timeout[p][q]]]
  /\ UNCHANGED <<timeout, pending>>

\* Receive messages: reset last-heard, clear suspicion, and raise the timeout
\* for any sender that was previously suspected (adaptive timeout).
Receive(p) ==
  /\ \E m \in pending[p] :
        /\ m.to = p
        /\ pending' = [pending EXCEPT ![p] = @ \ {m}]
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![p][m.from] =
                         IF m.from \in suspect[p] THEN timeout[p][m.from] + 1
                         ELSE timeout[p][m.from]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

ClockBound(p) ==
  /\ clock[p] > PredictPoint
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<timeout, lastHeard, suspect, pending>>

Next ==
  \E p \in Proc :
     \/ SendAlive(p)
     \/ Predict(p)
     \/ Receive(p)
     \/ ClockBound(p)

Spec ==
  /\ Init
  /\ [][Next]_<<clock, timeout, lastHeard, suspect, pending>>
  /\ WF_Vars(\E p \in Proc : Receive(p))

\* No stale suspicion: if p suspects q, it has actually timed out waiting.
NoStaleSuspicion ==
  \A p \in Proc, q \in Proc : (q \in suspect[p]) => (lastHeard[p][q] > timeout[p][q])

\* Progress: a correct process is eventually cleared from every suspicion set.
EventualClear ==
  \A q \in Proc : <>(\A p \in Proc : q \notin suspect[p])

====