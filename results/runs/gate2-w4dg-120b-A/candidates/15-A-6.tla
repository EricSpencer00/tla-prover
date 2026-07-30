---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* N must be greater than 3T for the quorum arithmetic to hold; those constraints
\* are enforced below (together with the bounds on T and F from the description).
CONSTANTS
  CorrectLoc, FaultyLoc, InitRecv, NotRecv, EchoSent, Accepted

VARIABLES correct, faulty, loc, recv, sent

vars == <<correct, faulty, loc, recv, sent>>

Locs == {CorrectLoc, FaultyLoc, InitRecv, NotRecv, EchoSent, Accepted}
Echos == {"ECHO"}

InitLoc == IF InitRecv \in Locs THEN InitRecv ELSE NotRecv

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ loc \in [1..N -> Locs]
  /\ recv \in [1..N -> SUBSET (1..N \X Echos)]
  /\ sent \subseteq (1..N \X Echos)

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ loc = [p \in 1..N |-> InitLoc]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A restricted initial state where no correct process received the broadcast.
QuietInit ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ loc = [p \in 1..N |-> NotRecv]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process may receive new messages any time, mixing the messages
\* actually sent by correct processes with arbitrary messages from the Byzantines.
Receive(p) ==
  /\ loc[p] \in {InitRecv, NotRecv, EchoSent}
  /\ \E m \in SUBSET (([1..N -> BOOLEAN] \X {Echos}) \union ([faulty -> BOOLEAN] \X {Echos})) :
       recv' = [recv EXCEPT ![p] = recv[p] \union m]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* A process that received the broadcast INIT accepts and sends an ECHO immediately.
AcceptInit(p) ==
  /\ loc[p] = InitRecv
  /\ loc' = [loc EXCEPT ![p] = Accepted]
  /\ sent' = sent \union {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A process that has not yet sent ECHO receives a "large but not yet decisive"
\* number of ECHO messages and sends its own without accepting.
EchoMid(p) ==
  /\ loc[p] = NotRecv
  /\ Cardinality({i \in 1..N : <<i, "ECHO">> \in recv[p]}) >= (N - 2 * T)
  /\ Cardinality({i \in 1..N : <<i, "ECHO">> \in recv[p]}) < (N - T)
  /\ loc' = [loc EXCEPT ![p] = EchoSent]
  /\ sent' = sent \union {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A process that has not yet sent ECHO receives a "decisive" number of ECHO
\* messages and accepts as it sends its own.
EchoDecisive(p) ==
  /\ loc[p] = NotRecv
  /\ Cardinality({i \in 1..N : <<i, "ECHO">> \in recv[p]}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = Accepted]
  /\ sent' = sent \union {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A process that already sent ECHO accepts once it receives the decisive number.
AcceptLate(p) ==
  /\ loc[p] = EchoSent
  /\ Cardinality({i \in 1..N : <<i, "ECHO">> \in recv[p]}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = Accepted]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in 1..N : Receive(p) \/ AcceptInit(p) \/ EchoMid(p) \/ EchoDecisive(p) \/ AcceptLate(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : Receive(p))

\* Unforgeability: without any correct broadcast, no correct process accepts.
UnforgLtl ==
  ( \A p \in correct : loc[p] = InitRecv )
    ~>
      ( \A p \in correct : loc[p] = Accepted )
  /\ ( \A p \in correct : loc[p] # InitRecv )
    ~> ( \A p \in correct : loc[p] # Accepted )

CorrLtl == ( \A p \in correct : loc[p] = InitRecv ) ~> ( \A p \in correct : loc[p] = Accepted )
RelayLtl == ( \E p \in correct : loc[p] = Accepted ) ~> ( \A p \in correct : loc[p] = Accepted )

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Locs = {CorrectLoc, FaultyLoc, InitRecv, NotRecv, EchoSent, Accepted}

====