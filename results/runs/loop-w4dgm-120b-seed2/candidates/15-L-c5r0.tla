---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process may be in four states: InitRecv (it got the broadcaster's INIT
\* message), NoInit (it never saw the broadcast), Sent (it sent an ECHO),
\* or Accepted (it delivered the broadcast).
Nodes == 0..(N - 1)
MsgTypes == {"ECHO"}
\* initState models the two possible starting worlds: with or without the
\* broadcaster's INIT message delivered to correct processes.
InitStates == {"InitRecv", "NoInit"}

VARIABLES correct, faulty, loc, recv, sent

vars == <<correct, faulty, loc, recv, sent>>

TypeOK ==
  /\ correct \subseteq Nodes /\ faulty \subseteq Nodes
  /\ loc \in [Nodes -> {"InitRecv", "NoInit", "Sent", "Accepted"}]
  /\ recv \in [Nodes -> SUBSET (Nodes \X MsgTypes)]
  /\ sent \subseteq (Nodes \X MsgTypes)

Init ==
  /\ correct = {i \in Nodes : i >= F}
  /\ faulty = {i \in Nodes : i < F}
  /\ loc = [i \in Nodes |-> InitStates[IF i >= F THEN 1 ELSE 2]]
  /\ recv = [i \in Nodes |-> {}]
  /\ sent = {}

NoBroadcast ==
  /\ \A i \in Nodes : loc[i] = "NoInit"
  /\ UNCHANGED <<correct, faulty, loc, recv, sent>>

InitRecv ==
  /\ \E i \in correct : loc[i] = "InitRecv"
  /\ UNCHANGED <<correct, faulty, loc, recv, sent>>

\* Faulty processes may send arbitrary ECHO messages that simply clog the
\* network; they never affect the quorum calculations.
FaultyMsgs == {<<i, mtype>> : i \in faulty, mtype \in MsgTypes}

\* A correct process may receive any subset of the messages sent so far
\* (from correct processes) plus any possible messages from faulties.
Receive(i) ==
  /\ loc[i] \in {"InitRecv", "NoInit"}
  /\ \E m \in SUBSET (sent \cup FaultyMsgs) :
       /\ recv' = [recv EXCEPT ![i] = recv[i] \cup m]
       /\ UNCHANGED <<correct, faulty, loc, sent>>
  /\ \A j \in correct : ("ECHO" \in {mtype : <<j, mtype>> \in recv[i]})
       => loc' = [loc EXCEPT ![i] = "Sent"]
  /\ sent' = sent \cup {<<i, "ECHO">}

\* Broadcast receipt: the process accepts immediately and sends its ECHO.
AcceptBroadcast(i) ==
  /\ loc[i] = "InitRecv"
  /\ loc' = [loc EXCEPT ![i] = "Accepted"]
  /\ sent' = sent \cup {<<i, "ECHO">}}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not sent an ECHO yet receives at least N-2T
\* but fewer than N-T echo messages and sends its own (it still cannot
\* accept, since the echo sub-quorum is not sufficient).
SendEchoPartial(i) ==
  /\ loc[i] \in {"NoInit", "Sent"}
  /\ Cardinality({j \in correct : <<j, "ECHO">> \in recv[i]}) >= (N - 2 * T)
  /\ Cardinality({j \in correct : <<j, "ECHO">> \in recv[i]}) < (N - T)
  /\ sent' = sent \cup {<<i, "ECHO">}}
  /\ loc' = [loc EXCEPT ![i] = "Sent"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process receiving the full quorum (N-T) accepts and sends its
\* ECHO, if it has not already sent one.
SendEchoFull(i) ==
  /\ loc[i] \in {"NoInit", "Sent"}
  /\ Cardinality({j \in correct : <<j, "ECHO">> \in recv[i]}) >= (N - T)
  /\ sent' = sent \cup {<<i, "ECHO">}}
  /\ loc' = [loc EXCEPT ![i] = "Accepted"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that already sent an ECHO accepts once it holds the
\* full quorum (it is just waiting on messages from the Byzantine ones).
AcceptEcho(i) ==
  /\ loc[i] = "Sent"
  /\ Cardinality({j \in correct : <<j, "ECHO">> \in recv[i]}) >= (N - T)
  /\ loc' = [loc EXCEPT ![i] = "Accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ NoBroadcast \/ InitRecv
  \/ \E i \in Nodes : Receive(i) \/ AcceptBroadcast(i)
                     \/ SendEchoPartial(i) \/ SendEchoFull(i) \/ AcceptEcho(i)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(InitRecv)
  /\ WF_vars(\E i \in Nodes : Receive(i))
  /\ WF_vars(\E i \in Nodes : AcceptBroadcast(i) \/ SendEchoFull(i) \/ AcceptEcho(i))

\* Unforgeability: when no correct process received the broadcaster's INIT
\* message, no correct process ever accepts the broadcast.
UnforgLtl == InitRecv ~> InitRecv

CorrLtl == InitRecv ~> (\A i \in correct : loc[i] = "Accepted")
RelayLtl == (\E i \in correct : loc[i] = "Accepted")
              ~> (\A i \in correct : loc[i] = "Accepted")

FCConstraints ==
  /\ correct \cup faulty = Nodes /\ correct \cap faulty = {}
  /\ Cardinality(correct) = N - F
  /\ N > 3 * T /\ T >= F /\ F >= 0
====