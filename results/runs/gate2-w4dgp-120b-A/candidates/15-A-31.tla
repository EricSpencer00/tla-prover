---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, inbox, sent
vars == <<correct, faulty, pc, inbox, sent>>

\* pc: control location per process; inbox: messages received per process; sent:
\* messages sent by correct processes. Message type is always "ECHO".
InitMsgs == {1, 2}
TypeOK ==
  /\ correct \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> {"startNo", "startYes", "sent", "accept"}]
  /\ inbox \in [1..N -> SUBSET (1..N \times {"ECHO"})]
  /\ sent \subseteq (1..N \times {"ECHO"})

Init ==
  /\ correct \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> {"startNo", "startYes"}]
  /\ inbox = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process whose broadcast was never received starts in startNo.
InitNoBroadcast ==
  /\ Init
  /\ \A p \in correct : pc[p] = "startNo"
  /\ TRUE

\* A correct process whose broadcast was received starts in startYes.
InitBroadcast ==
  /\ Init
  /\ \A p \in correct : pc[p] = "startYes"
  /\ TRUE

\* Receiving a fresh batch of messages: all sent by correct processes plus any
\* message a Byzantine process may forge (unrestricted set of senders).
ReceiveMsgs(p) ==
  /\ LET new ==
       {q \in 1..N |-> IF q \in correct
                     THEN {<<q, "ECHO">>}
                     ELSE UNION {<<q, "ECHO">> : m \in sent}}
     IN inbox' = [inbox EXCEPT ![p] = inbox[p] \cup new[p]]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* Immediate acceptance by the broadcaster (the INIT-receiver).
InitAccept(p) ==
  /\ pc[p] = "startYes"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

FwdMsg(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality({q \in 1..N : <<q, "ECHO">> \in inbox[p]}) >= N - 2 * T
  /\ Cardinality({q \in 1..N : <<q, "ECHO">> \in inbox[p]}) < N - T
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, pc, inbox>>

AcceptViaQuorum(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality({q \in 1..N : <<q, "ECHO">> \in inbox[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

RelayAccept(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality({q \in 1..N : <<q, "ECHO">> \in inbox[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

Next ==
  \/ \E p \in correct :
       ReceiveMsgs(p) \/ InitAccept(p) \/ FwdMsg(p) \/ AcceptViaQuorum(p) \/ RelayAccept(p)

Spec == Init /\ [][Next]_vars

CorrLtl ==
  /\ InitBroadcast => <>(\A p \in correct : pc[p] = "accept")
  /\ (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

UnforgLtl == InitNoBroadcast => [](pc[CHOOSE p \in correct : TRUE] # "accept")
RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

SpecNoFair == Init /\ [][Next]_vars

====