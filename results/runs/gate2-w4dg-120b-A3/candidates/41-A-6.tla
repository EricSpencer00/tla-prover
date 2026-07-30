---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,          \* the processes in the system
  d0,            \* the default timeout interval
  SendPoint,     \* the clock value at which alive messages are sent
  PredictPoint,  \* the clock value at which predictions are made
  Messages       \* the message type (every process addresses one message to another)

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # PredictPoint

VARIABLES
  suspected,    \* [Proc -> SUBSET Proc]  processes each process currently suspects
  timeout,      \* [Proc -> [Proc -> Nat]] adaptive timeout for each peer of each process
  lastHeard,    \* [Proc -> [Proc -> Nat]] clock ticks since each process last heard from each peer
  clock,        \* [Proc -> Nat]  local clock for each process
  toSend        \* [Proc -> SUBSET Messages] outgoing messages each process is about to send

vars == << suspected, timeout, lastHeard, clock, toSend >>

TypeOK ==
  /\ suspected \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ toSend \in [Proc -> SUBSET Messages]

\* An alive message addressed to a peer: every process holds one such message for each peer.
Messages == { [from |-> p, to |-> q] : p \in Proc, q \in Proc, p # q }

Init ==
  /\ suspected = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ toSend = [p \in Proc |-> {}]

\* A process sends an alive message to every other process at the send interval.
SendAlive(p) ==
  /\ clock[p] = SendPoint
  /\ clock[p] # PredictPoint
  /\ toSend' = [toSend EXCEPT ![p] = { m \in Messages : m.from = p }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p][q] = IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] : q \in Proc]
  /\ UNCHANGED << suspected, timeout >>

\* A process adds to its suspicion set every peer it has not heard from past the timeout.
Predict(p) ==
  /\ clock[p] = PredictPoint
  /\ clock[p] # SendPoint
  /\ suspected' = [suspected EXCEPT ![p] = { q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q] } \cup suspected[p]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p][q] = IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] : q \in Proc]
  /\ UNCHANGED << timeout, toSend >>

\* Every other clock value is for receiving: counters reset, suspicions cleared, timeouts adapt.
Receive(p) ==
  /\ ~(clock[p] = SendPoint /\ clock[p] # PredictPoint)
  /\ ~(clock[p] = PredictPoint /\ clock[p] # SendPoint)
  /\ \E msgs \in toSend[p] :
        /\ lastHeard' = [lastHeard EXCEPT ![p][msgs.to] = 0]
        /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \ { msgs.to }]
        /\ timeout' = [timeout EXCEPT ![p][msgs.to] = IF msgs.from \in suspected[p] THEN timeout[p][msgs.to] + 1 ELSE timeout[p][msgs.to]]
  /\ toSend' = [toSend EXCEPT ![p] = {}]
  /\ clock' = IF clock[p] > 0 /\ \A q \in Proc : clock[p] > timeout[p][q] /\ clock[p] > SendPoint /\ clock[p] > PredictPoint
                THEN 0 ELSE clock[p] + 1
  /\ UNCHANGED << \* every variable touched above is already \E'd or assigned, so none left
                    \* UNCHANGED here; this clause exists for syntax only
                    >>
  /\ UNCHANGED << >>  \* syntactically needed after the \E in Receive

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Proc : SendAlive(p))
  /\ WF_vars(\E p \in Proc : Predict(p))

====