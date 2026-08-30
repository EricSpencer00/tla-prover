---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Bump(pc) == IF pc < 4 THEN pc + 1 ELSE pc

VARIABLES correct, faulty, pc, recv, sent
vars == <<correct, faulty, pc, recv, sent>>

Messages == {"echo"}
Senders == 1..N
InitMsgs == {"init"}
Pairs == Senders \X Messages

TypeOK ==
  /\ correct \subseteq Senders /\ faulty \subseteq Senders
  /\ Cardinality(correct) = N - F
  /\ faulty = Senders \ correct
  /\ pc \in [Senders -> 0..4]
  /\ recv \in [Senders -> SUBSET Pairs]
  /\ sent \subseteq Pairs

\* No correct process broadcasts: nobody accepts.
UnforgLtl ==
  (\A q \in Senders : q \in correct => pc[q] \in {1, 2})
    ~> (\A q \in Senders : q \in correct => pc[q] \in {0, 1})

FCConstraints == TypeOK

InitRecv ==
  (\E S \in SUBSET Senders :
     /\ S # {}
     /\ \A q \in Senders : pc[q] = (IF q \in S THEN 2 ELSE 1))
       /\ \A q \in Senders : recv[q] = IF q \in S THEN {<<q, "init">>} ELSE {}

Init ==
  /\ correct \subseteq Senders /\ faulty \subseteq Senders
  /\ pc = [q \in Senders |-> IF q \in correct /\ q \in (1..(N - F)) THEN 2 ELSE 1]
  /\ recv = InitRecv
  /\ sent = {}

\* A restricted start: no correct process received the INIT broadcast.
InitNone ==
  /\ correct \subseteq Senders /\ faulty \subseteq Senders
  /\ pc = [q \in Senders |-> IF q \in correct THEN 1 ELSE 0]
  /\ recv = [q \in Senders |-> {}]
  /\ sent = {}

\* A correct process may receive any set of new messages at once.
Receive(q) ==
  /\ q \in correct /\ pc[q] < 3
  /\ \E M \in SUBSET Pairs :
       recv' = [recv EXCEPT ![q] = @ \cup M]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* The broadcasted INIT message forces immediate accept-and-echo.
AcceptInit(q) ==
  /\ q \in correct /\ pc[q] = 2 /\ pc' = [pc EXCEPT ![q] = Bump(@)]
  /\ sent' = sent \cup {<<q, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* 1st threshold: send ECHO, do not accept yet.
Echo1(q) ==
  /\ q \in correct /\ pc[q] = 0
  /\ Cardinality({y \in Senders : <<y, "echo">> \in recv[q]}) >= N - 2 * T
  /\ Cardinality({y \in Senders : <<y, "echo">> \in recv[q]}) < N - T
  /\ pc' = [pc EXCEPT ![q] = Bump(@)]
  /\ sent' = sent \cup {<<q, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* 2nd threshold: send ECHO and accept.
Echo2(q) ==
  /\ q \in correct /\ pc[q] = 0
  /\ Cardinality({y \in Senders : <<y, "echo">> \in recv[q]}) >= N - T
  /\ pc' = [pc EXCEPT ![q] = Bump(@)]
  /\ sent' = sent \cup {<<q, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* Already ECHOed: accept once the 2nd threshold is reached.
AcceptEcho(q) ==
  /\ q \in correct /\ pc[q] = 3
  /\ Cardinality({y \in Senders : <<y, "echo">> \in recv[q]}) >= N - T
  /\ pc' = [pc EXCEPT ![q] = Bump(@)]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E q \in Senders : Receive(q) \/ AcceptInit(q) \/ Echo1(q) \/ Echo2(q)
  \/ \E q \in Senders : AcceptEcho(q)

Spec == Init /\ [][Next]_vars
  /\ \A q \in Senders : WF_vars(Receive(q)) /\ WF_vars(AcceptEcho(q))
  /\ \A q \in Senders : SF_vars(AcceptInit(q)) /\ SF_vars(Echo1(q)) /\ SF_vars(Echo2(q))

CorrLtl == \A q \in Senders : (q \in correct) ~> (q \in correct /\ pc[q] \in {2, 3, 4})
RelayLtl == (\E q \in Senders : q \in correct /\ pc[q] \in {2, 3, 4})
  ~> (\A q \in Senders : q \in correct => pc[q] \in {2, 3, 4})

====