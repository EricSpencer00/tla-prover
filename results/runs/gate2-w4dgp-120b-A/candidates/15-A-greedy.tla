---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A one-round reliable broadcast (Srikanth & Toueg 1987) with up to T Byzantine
\* processes.  The broadcaster is modeled by an initial value per process: a
\* process either starts having received the INIT message or not.
\* Correct processes send at most one ECHO message each; Byzantine processes may
\* send arbitrary ECHO messages, so the set of messages a process can receive is
\* the union of all correct-process messages and all possible Byzantine messages.

Processes == 1..N
Msgs == {"ECHO"}
Pairs == [snd : Processes, typ : Msgs]

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty \subseteq Processes
  /\ pc \in [Processes -> {"init","noinit","echoed","accepted"}]
  /\ recv \in [Processes -> SUBSET Pairs]
  /\ sent \subseteq Pairs

\* The broadcaster is not a distinguished process: the set of processes that
\* received its INIT message is chosen nondeterministically at Init.
Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = Processes \ correct
  /\ \E initSet \subseteq Processes :
       /\ Cardinality(initSet) = N - F
       /\ pc = [p \in Processes |-> IF p \in initSet THEN "init" ELSE "noinit"]
  /\ recv = [p \in Processes |-> {}]
  /\ sent = {}

\* A restricted initial state for checking the no-broadcast case: no correct
\* process receives the INIT message.
InitNoBroadcast ==
  /\ Cardinality(correct) = N - F
  /\ faulty = Processes \ correct
  /\ pc = [p \in Processes |-> "noinit"]
  /\ recv = [p \in Processes |-> {}]
  /\ sent = {}

\* A correct process may receive any subset of the messages that have been sent
\* by correct processes, plus any possible Byzantine message.
Receive(p) ==
  /\ p \in correct
  /\ pc[p] \in {"init","noinit","echoed","accepted"}
  /\ \E newMsgs \subseteq (sent \cup Pairs) :
       recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct process that received the broadcaster's INIT message immediately
\* accepts and sends its ECHO message.
InitAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO receives enough (N-2T) but not
\* enough (N-T) ECHO messages to send its own ECHO without yet accepting.
EchoPartial(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) >= N - 2 * T
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO receives enough (N-T) ECHO
\* messages to send its own ECHO and accept immediately.
EchoAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has already sent ECHO receives enough (N-T) ECHO
\* messages to accept.
Accept(p) ==
  /\ p \in correct
  /\ pc[p] = "echoed"
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in Processes : Receive(p)
  \/ \E p \in Processes : InitAccept(p)
  \/ \E p \in Processes : EchoPartial(p)
  \/ \E p \in Processes : EchoAccept(p)
  \/ \E p \in Processes : Accept(p)

\* Fairness is needed only for the receive-and-act steps of correct processes;
\* the no-broadcast safety check does not require it.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in correct : WF_vars(Receive(p))
  /\ \A p \in correct : WF_vars(InitAccept(p))
  /\ \A p \in correct : WF_vars(EchoPartial(p))
  /\ \A p \in correct : WF_vars(EchoAccept(p))
  /\ \A p \in correct : WF_vars(Accept(p))

SpecNoBroadcast ==
  /\ InitNoBroadcast
  /\ [][Next]_vars
  /\ \A p \in correct : WF_vars(Receive(p))
  /\ \A p \in correct : WF_vars(InitAccept(p))
  /\ \A p \in correct : WF_vars(EchoPartial(p))
  /\ \A p \in correct : WF_vars(EchoAccept(p))
  /\ \A p \in correct : WF_vars(Accept(p))

\* Correctness: if every correct process received the broadcaster's INIT
\* message, then every correct process eventually accepts.
CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accepted")

\* Relay: if any correct process accepts, then all correct processes accept.
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")

\* Unforgeability: if no correct process broadcasts (none received the INIT
\* message), then no correct process ever accepts.
UnforgLtl == (\A p \in correct : pc[p] = "noinit") ~> (\A p \in correct : pc[p] # "accepted")

\* The model requires N > 3T (the bound under which the protocol is correct),
\* T >= F (the number of Byzantine processes), and F >= 0.
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====