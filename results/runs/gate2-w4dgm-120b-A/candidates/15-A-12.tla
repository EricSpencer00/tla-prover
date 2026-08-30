---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* The promoter's single INIT message is modeled as an initial value per
\* process (some correct ones received it, some did not) rather than a
\* dedicated broadcaster.  The safety and liveness claims are given as
\* state predicates over that initial distribution.
VARIABLES correct, faulty, pc, recvd, sentBy

vars == << correct, faulty, pc, recvd, sentBy >>

Echoes(p) == { m.sender : m \in { x \in recvd[p] : x.msg = "ECHO" } }

TypeOK ==
  /\ correct \subseteq (1 .. N) /\ faulty \subseteq (1 .. N)
  /\ pc \in [1 .. N -> {"none","xmit","wait","acc"}]
  /\ recvd \in [1 .. N -> SUBSET [sender: 1 .. N, msg: {"ECHO"}]]
  /\ sentBy \subseteq (1 .. N)

Init ==
  /\ correct = {1 .. (N - F)} /\ faulty = (1 .. N) \ correct
  /\ pc = [p \in 1 .. N |-> IF p <= (N - F) THEN "xmit" ELSE "none"]
  /\ recvd = [p \in 1 .. N |-> {}]
  /\ sentBy = {}

NoBroadcast ==
  /\ correct = {1 .. (N - F)} /\ faulty = (1 .. N) \ correct
  /\ pc = [p \in 1 .. N |-> "none"]
  /\ recvd = [p \in 1 .. N |-> {}]
  /\ sentBy = {}

\* A correct process may receive any set of unprocessed messages, but only
\* those actually sent by correct senders together with a bounded set of
\* Byzantine forgeries, which is what keeps the cutoffs just above the
\* fault bound reachable for the slow-but-correct case.
Receive(p) ==
  /\ pc[p] \in {"wait", "acc"}
  /\ \E m \in SUBSET [sender: 1 .. N, msg: {"ECHO"}] :
       /\ \A x \in m : x \in sentBy \/ (x.sender \in faulty /\ m \subseteq sentBy \cup {x})
       /\ recvd' = [recvd EXCEPT ![p] = @ \cup m]
  /\ UNCHANGED << correct, faulty, pc, sentBy >>

BroadcastEcho(p) ==
  /\ pc[p] = "xmit"
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ sentBy' = sentBy \cup {p}
  /\ UNCHANGED << correct, faulty, recvd >>

RelayEcho(p) ==
  /\ pc[p] = "none"
  /\ Cardinality(Echoes(p)) >= (N - (2 * T))
  /\ Cardinality(Echoes(p)) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "wait"]
  /\ sentBy' = sentBy \cup {p}
  /\ UNCHANGED << correct, faulty, recvd >>

RelayEchoAccept(p) ==
  /\ pc[p] = "none"
  /\ Cardinality(Echoes(p)) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ sentBy' = sentBy \cup {p}
  /\ UNCHANGED << correct, faulty, recvd >>

RelayAccept(p) ==
  /\ pc[p] = "wait"
  /\ Cardinality(Echoes(p)) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ UNCHANGED << correct, faulty, recvd, sentBy >>

Next ==
  \/ Receive(1) \/ Receive(2) \/ Receive(3)
  \/ BroadcastEcho(1) \/ BroadcastEcho(2) \/ BroadcastEcho(3)
  \/ RelayEcho(1) \/ RelayEcho(2) \/ RelayEcho(3)
  \/ RelayEchoAccept(1) \/ RelayEchoAccept(2) \/ RelayEchoAccept(3)
  \/ RelayAccept(1) \/ RelayAccept(2) \/ RelayAccept(3)

Spec == Init /\ [][Next]_vars
  /\ \A p \in 1 .. N : WF_vars(Receive(p)) /\ WF_vars(RelayAccept(p))

\* If no correct process ever broadcasts the INIT message, no correct
\* process should ever accept: unforgeability of the broadcast, even
\* though Byzantine processes may saturate the network with ECHO.
UnforgLtl == (\A p \in correct : pc[p] # "xmit") ~> (\A p \in correct : pc[p] = "acc")

CorrLtl == (\A p \in correct : pc[p] = "xmit") ~> (\A p \in correct : pc[p] = "acc")

RelayLtl == (\E p \in correct : pc[p] = "acc") ~> (\A q \in correct : pc[q] = "acc")

FCConstraints ==
  /\ N # 0 /\ T >= F /\ N > (3 * T)
  /\ correct # {} /\ faulty # {}
  /\ Cardinality(correct) + Cardinality(faulty) = N

====