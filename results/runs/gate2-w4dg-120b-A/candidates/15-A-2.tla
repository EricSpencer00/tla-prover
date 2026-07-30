---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Process control locations: recv0/recv1 mean not yet sent ECHO, recv1 means the
\* INIT message was received; sent means the process sent an ECHO; accept means
\* the process has delivered the broadcast. mset[p] records messages p has
\* received; sendSet records every message actually sent by a correct process.
VARIABLES correct, faulty, loc, mset, sendSet

InitState == "init"
BcastState == "bcast"
NoECHO == "none"
SentECHO == "echo"
Accepted == "accept"

AllProcesses == 1..N
Msgs == {<<i, "ECHO">> : i \in AllProcesses}
FromCorrect(p) == {<<i, "ECHO">> : i \in correct}
FromFaulty(p) == {<<i, "ECHO">> : i \in faulty}
FromAll(p) == FromCorrect(p) \cup FromFaulty(p)
ECHOCount(p, s) == Cardinality(mset[p] \cap {<<q, "ECHO">> : q \in s})

Q2 == N - 2 * T
QT == N - T

TypeOK ==
  /\ correct \subseteq AllProcesses
  /\ faulty \subseteq AllProcesses
  /\ loc \in [AllProcesses -> {InitState, BcastState, NoECHO, SentECHO, Accepted}]
  /\ mset \in [AllProcesses -> SUBSET Msgs]
  /\ sendSet \subseteq Msgs

\* Unforgeability: if no correct process broadcasts (all start in the
\* non-broadcast state), no correct process ever accepts.
FCConstraints ==
  /\ (loc["init"] = BcastState) \/ (loc["init"] = InitState)
  /\ \A p \in correct : loc[p] \in {InitState, BcastState, NoECHO, SentECHO, Accepted}
  /\ \A p \in AllProcesses : loc[p] = Accepted => loc[p] \in {SentECHO, Accepted}
  /\ \A p \in correct : mset[p] \subseteq SendSet

Init ==
  /\ correct \subseteq AllProcesses /\ Cardinality(correct) = N - F
  /\ faulty = AllProcesses \ correct
  /\ loc = [p \in AllProcesses |->
              IF p \in correct THEN InitState ELSE NoECHO]
  /\ mset = [p \in AllProcesses |-> {}]
  /\ sendSet = {}

\* A restricted initial state where no correct process received the broadcast.
InitNoBroad ==
  /\ correct \subseteq AllProcesses /\ Cardinality(correct) = N - F
  /\ faulty = AllProcesses \cap correct
  /\ loc = [p \in AllProcesses |-> InitState]
  /\ mset = [p \in AllProcesses |-> {}]
  /\ sendSet = {}

\* A correct process receives a set of new messages; messages may come from
\* any correct sender or from Byzantine faulty processes.
RecvMsg(p) ==
  /\ loc[p] \in {InitState, BcastState}
  /\ \E s \in SUBSET FromAll(p) :
       /\ mset' = [mset EXCEPT ![p] = s]
  /\ UNCHANGED <<correct, faulty, loc, sendSet>>

\* A correct process that received the broadcast INIT message sends an ECHO
\* and immediately accepts.
SendEcho(p) ==
  /\ loc[p] = InitState
  /\ loc' = [loc EXCEPT ![p] = Accepted]
  /\ mset' = [mset EXCEPT ![p] = FromCorrect(p)]
  /\ sendSet' = sendSet \cup FromCorrect(p)
  /\ UNCHANGED <<correct, faulty>>

\* A correct process that has not yet sent ECHO receives at least N-2T but
\* fewer than N-T ECHO messages, so it sends ECHO but does not yet accept.
SendEchoMid(p) ==
  /\ loc[p] = InitState
  /\ ECHOCount(p, correct) >= Q2
  /\ ECHOCount(p, correct) < QT
  /\ loc' = [loc EXCEPT ![p] = SentECHO]
  /\ mset' = [mset EXCEPT ![p] = FromCorrect(p)]
  /\ sendSet' = sendSet \cup FromCorrect(p)
  /\ UNCHANGED <<correct, faulty>>

\* A correct process that has not yet sent ECHO receives at least N-T ECHO
\* messages, so it sends ECHO and immediately accepts.
SendEchoAccept(p) ==
  /\ loc[p] = InitState
  /\ ECHOCount(p, correct) >= QT
  /\ loc' = [loc EXCEPT ![p] = Accepted]
  /\ mset' = [mset EXCEPT ![p] = FromCorrect(p)]
  /\ sendSet' = sendSet \cup FromCorrect(p)
  /\ UNCHANGED <<correct, faulty>>

\* A correct process that already sent ECHO accepts once it receives N-T ECHO.
Accept(p) ==
  /\ loc[p] = SentECHO
  /\ ECHOCount(p, correct) >= QT
  /\ loc' = [loc EXCEPT ![p] = Accepted]
  /\ UNCHANGED <<correct, faulty, mset, sendSet>>

Next ==
  \E p \in AllProcesses :
    \/ RecvMsg(p) \/ SendEcho(p) \/ SendEchoMid(p)
    \/ SendEchoAccept(p) \/ Accept(p)

\* Weak fairness on the combined receive-and-act steps of correct processes.
Spec ==
  /\ Init
  /\ [][Next]_<<correct, faulty, loc, mset, sendSet>>
  /\ \A p \in correct :
       SF_vars(RecvMsg(p)) /\ SF_vars(SendEcho(p))
       /\ SF_vars(SendEchoMid(p)) /\ SF_vars(SendEchoAccept(p))
       /\ SF_vars(Accept(p))

CorrLtl ==
  /\ (loc["init"] = BcastState)
  /\ (\A p \in correct : <>(loc[p] = Accepted))

RelayLtl ==
  \E p \in correct : (loc[p] = Accepted) ~> (\A q \in correct : loc[q] = Accepted)

UnforgLtl ==
  /\ (loc["init"] = InitState)
  /\ (\A p \in correct : loc[p] # Accepted)
  /\ (\A p \in correct : loc[p] = InitState)

====