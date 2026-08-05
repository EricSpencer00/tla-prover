---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME d0 \in Nat /\ SendPoint \in Nat /\ PredictPoint \in Nat
ASSUME SendPoint > 0 /\ PredictPoint > 0
ASSUME SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0

VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

Bump(p, r) ==
  LET c == CHOOSE c \in r : p \in c.dest AND c \notin outgoing
  IN <<c.dest, c.s>>
BumpAny == CHOOSE c \in Messages : c \notin outgoing

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
  /\ outgoing' = outgoing \cup {[dest |-> q, s |-> p] : q \in Proc \ {p}}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |->
                      IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |->
                      IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outgoing>>

\* The environment may deliver any subset of the messages in transit.
Receive(p) ==
  /\ \A q \in Proc \ {p} : lastHeard[p][q] <= timeout[p][q]
  /\ \A c \in Messages : c \in outgoing => c.s = p
  /\ \E r \in SUBSET {c \in outgoing : c.s = p} :
       /\ \A c \in r : lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |->
                                   IF q = c.dest THEN 0 ELSE lastHeard[p][q]]]
                          \* A message from a suspected process bumps its timeout.
                          \* A message received from a non-crashed process is proof
                          \* it has not crashed, so the process is removed from the suspect set.
                       suspect' = [suspect EXCEPT ![p] = suspect[p] \ {c.dest}]
                       timeout' = IF c.dest \in suspect[p]
                                    THEN [timeout EXCEPT ![p][c.dest] = timeout[p][c.dest] + 1]
                                    ELSE timeout
                       outgoing' = outgoing \ r
       /\ UNCHANGED clock

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

TypeOK ==
  /\ \A p \in Proc : lastHeard[p] \in [Proc \ {p} -> 0 .. 3]
  /\ \A p \in Proc : timeout[p] \in [Proc \ {p} -> Nat]
  /\ \A p \in Proc : suspect[p] \subseteq Proc
  /\ outgoing \subseteq Messages
====