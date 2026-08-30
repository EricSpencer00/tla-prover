---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,       \* the process set
  d0,         \* default timeout interval
  SendPoint,  \* clock value that triggers sending alive messages
  PredictPoint, \* clock value that triggers making predictions
  Messages    \* the set of alive messages

Message == [src : Proc, dst : Proc]

VARIABLES
  suspect,    \* suspect[p]: set of processes p currently suspects as crashed
  timeout,    \* timeout[p]: [Proc -> Nat] adaptive timeout intervals per process
  lastHeard,  \* lastHeard[p]: [Proc -> Nat] ticks since p last heard from each process
  clock,      \* local clock per process
  outbox      \* outbox[p]: set of alive messages p will send next

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Message]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Send alive messages at a send interval that never coincides with predict
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = { [src |-> p, dst |-> q] : q \in Proc, q # p }]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<suspect, timeout>>

\* Make predictions when the clock lands on the predict interval
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup
                   { q \in Proc : lastHeard[p][q] > timeout[p][q] /\ q # p }]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive incoming alive messages and adapt timeouts
Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q = p \/ lastHeard[p][q] >= timeout[p][q]
                          THEN @ ELSE @ + 1]]
  /\ suspect' = [q \in Proc |->
        LET attr == Cardinality({ m \in outbox[q] : m.dst = p })
        IN IF attr = 1
             THEN suspect[q] \ {p}
             ELSE IF p \in suspect[q]
                    THEN IF attr > 1
                            THEN suspect[q]
                            ELSE suspect[q] \ {p}
                    ELSE suspect[q]
        ]
  /\ timeout' = [q \in Proc |->
        LET attr == Cardinality({ m \in outbox[q] : m.dst = p })
        IN IF attr > 1 /\ p \in suspect[q]
             THEN @ + 1
             ELSE @]
  /\ outbox' = [q \in Proc |-> { m \in outbox[q] : m.dst # p }]
  /\ clock' = [clock EXCEPT ![p] =
        IF @ > SendPoint /\ @ > PredictPoint /\ @ > timeout[p][p]
          THEN 0 ELSE @ + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Proc : SendAlive(p))
  /\ WF_vars(\E p \in Proc : Predict(p))
  /\ WF_vars(\E p \in Proc : Receive(p))

\* Bounded counters stay within the natural numbers
Bounds ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> Nat]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET Message]

====