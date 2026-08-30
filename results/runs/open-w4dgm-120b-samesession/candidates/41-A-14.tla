---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, interval, ticksSince, clock, outbox

vars == <<suspicion, interval, ticksSince, clock, outbox>>

\* A message carries its sender and the tick it was sent at; the tick
\* value is irrelevant to correctness, so the channel is a set, not a queue.
Message == [sender : Proc, tick : 0 .. d0]

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ interval \in [Proc -> [Proc -> Nat]]
  /\ ticksSince \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Message]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ interval = [p \in Proc |-> [q \in Proc |-> 1]]
  /\ ticksSince = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] =
       {m \in outbox[p] : m.tick # clock[p]}
         \cup {[sender |-> q, tick |-> clock[p]] : q \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ ticksSince' = [ticksSince EXCEPT ![p] =
       [q \in Proc |-> IF q \in suspicion[p] THEN ticksSince[p][q] ELSE ticksSince[p][q] + 1]]
  /\ UNCHANGED <<suspicion, interval>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] =
       {q \in suspicion[p]} \cup
         {q \in Proc \ {p} :
           ticksSince[p][q] > interval[p][q]}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ ticksSince' = [ticksSince EXCEPT ![p] =
       [q \in Proc |-> IF q \in suspicion[p] THEN ticksSince[p][q] ELSE ticksSince[p][q] + 1]]
  /\ UNCHANGED <<interval, outbox>>

\* Receiving an alive message from a process it previously suspected expands
\* that process's timeout interval, so the suspicion never stabilizes there.
Receive(p, msgs) ==
  /\ outbox[p] # {}
  /\ outbox' = [outbox EXCEPT ![p] = @ \ msgs]
  /\ suspicion' = [suspicion EXCEPT ![p] =
       {q \in suspicion[p] : \A m \in msgs : m.sender # q}]
  /\ interval' = [q \in Proc |-> IF \E m \in msgs : m.sender = q /\ q \in suspicion[p]
                                  THEN interval[p][q] + 1 ELSE interval[p][q]]
  /\ ticksSince' = [ticksSince EXCEPT ![p] =
       [q \in Proc |-> IF \E m \in msgs : m.sender = q THEN 0 ELSE ticksSince[p][q]]]
  /\ UNCHANGED <<clock>>

Tick ==
  /\ \E p \in Proc :
       /\ clock[p] % SendPoint # 0
       /\ clock[p] % PredictPoint # 0
       /\ outbox[p] = {}
       /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= d0
                                     THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED <<suspicion, interval, ticksSince, outbox>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc, msgs \in SUBSET outbox[p] : Receive(p, msgs)
  \/ Tick

Spec == Init /\ [][Next]_vars

====