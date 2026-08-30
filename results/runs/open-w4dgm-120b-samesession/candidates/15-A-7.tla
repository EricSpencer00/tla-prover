---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct + faulty = the whole population, split nondeterministically at init.
VARIABLES correct, faulty, pc, recvd, sentMsgs

vars == <<correct, faulty, pc, recvd, sentMsgs>>

Parts == 0..(N - 1)

Message == [sender: Parts, kind: {"ECHO"}]
kc(e) == Cardinality({m \in e : m.kind = "ECHO"})

RECURSIVE FromSet(_)
FromSet(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x.sender} \cup FromSet(S \ {x})

TypeOK ==
  /\ correct \subseteq Parts
  /\ faulty \subseteq Parts
  /\ pc \in [Parts -> {"init","nobroadcast","sent","accepted"}]
  /\ recvd \in [Parts -> SUBSET Message]
  /\ sentMsgs \subseteq Message

Init ==
  /\ correct = {i \in Parts : i < (N - F)}
  /\ faulty = Parts \ correct
  /\ pc = [i \in Parts |-> IF i < (N - F) THEN "init" ELSE "nobroadcast"]
  /\ recvd = [i \in Parts |-> {}]
  /\ sentMsgs = {}

\* No broadcast at all: every correct process begins without INIT.
RestrictedInit ==
  /\ correct = {i \in Parts : i < (N - F)}
  /\ faulty = Parts \ correct
  /\ pc = [i \in Parts |-> "nobroadcast"]
  /\ recvd = [i \in Parts |-> {}]
  /\ sentMsgs = {}

\* Messages are drawn from every correct sender (always possible) plus all
\* possible Byzantine (faulty) senders (adversary's choice).
Receive(i) ==
  \E S \in SUBSET ({m \in sentMsgs : m.sender \in correct} \cup { [sender: j, kind: "ECHO"] : j \in faulty }) :
    recvd' = [recvd EXCEPT ![i] = @ \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

\* A process that got the INIT message accepts and relays immediately.
ActOnInit(i) ==
  /\ i \in correct
  /\ pc[i] = "init"
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> i, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvd>>

\* Merely enough distinct ECHOs to be allowed to relay, but not yet to decide.
Relay(i) ==
  /\ i \in correct
  /\ pc[i] = "nobroadcast"
  /\ kc(recvd[i]) >= (N - 2 * T)
  /\ kc(recvd[i]) < (N - T)
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> i, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvd>>

\* Decisively enough ECHOs to both relay and accept.
RelayAndAccept(i) ==
  /\ i \in correct
  /\ pc[i] = "nobroadcast"
  /\ kc(recvd[i]) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> i, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvd>>

Accept(i) ==
  /\ i \in correct
  /\ pc[i] = "sent"
  /\ kc(recvd[i]) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvd, sentMsgs>>

Next ==
  \/ Receive(0) \/ Receive(1) \/ Receive(2) \/ Receive(3)
  \/ ActOnInit(0) \/ ActOnInit(1) \/ ActOnInit(2) \/ ActOnInit(3)
  \/ Relay(0) \/ Relay(1) \/ Relay(2) \/ Relay(3)
  \/ RelayAndAccept(0) \/ RelayAndAccept(1) \/ RelayAndAccept(2) \/ RelayAndAccept(3)
  \/ Accept(0) \/ Accept(1) \/ Accept(2) \/ Accept(3)

Spec == Init /\ [][Next]_vars
        /\ (\A i \in Parts : WF_vars(Receive(i)))
        /\ (\A i \in Parts : WF_vars(ActOnInit(i)))
        /\ (\A i \in Parts : WF_vars(Relay(i)))
        /\ (\A i \in Parts : WF_vars(RelayAndAccept(i)))
        /\ (\A i \in Parts : WF_vars(Accept(i)))

\* Unforgeability: nothing can be accepted without at least one correct
\* process actually having broadcast the INIT message.
UnforgLtl == (\A i \in correct : pc[i] = "nobroadcast") ~> (\E i \in correct : pc[i] = "accepted")

CorrLtl == (\A i \in correct : pc[i] = "init") ~> (\A i \in correct : pc[i] = "accepted")

RelayLtl == (\E i \in correct : pc[i] = "accepted") ~> (\A i \in correct : pc[i] = "accepted")

\* Weak fairness on the combined receive-and-act steps of correct processes.
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ TypeOK

====