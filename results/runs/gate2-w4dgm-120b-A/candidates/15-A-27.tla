---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* bounded ceiling for the one-round protocol (messages are never reused)
MaxMsgs == 2 * N

VARIABLES correct, faulty, loc, recv, sent

vars == <<correct, faulty, loc, recv, sent>>

\* loc: which of the four protocol steps a correct process is at
TypeLoc == {"idle", "broadcast", "echoed", "accept"}

BroadcastMsgs == {<<p, "init">> : p \in 1..N}
EchoMsgs == {<<p, "echo">> : p \in 1..N}
ByzMsgs == {<<p, "bz">> : p \in 1..N}
AllMsgs == BroadcastMsgs \cup EchoMsgs \cup ByzMsgs

SentByCorrect == {<<p, "init">> : p \in correct} \cup EchoMsgs

InitStates == {"broadcast", "idle"}

RECURSIVE FromOf(_)
FromOf(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x[1]} \cup FromOf(S \ {x})

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ loc \in [1..N -> TypeLoc]
  /\ recv \in [1..N -> SUBSET AllMsgs]
  /\ sent \subseteq AllMsgs

\* safety: unforgeability, plus all variables staying in their domains
FCConstraints ==
  /\ TypeOK
  /\ ( (\A p \in correct : loc[p] # "broadcast") => (\A p \in correct : loc[p] # "accept") )
  /\ sent \subseteq AllMsgs
  /\ Cardinality(sent) <= MaxMsgs

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {(N - F + 1)..N}
  /\ loc \in [1..N -> InitStates]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* the restricted no-broadcast initial state (every correct process idle)
BroadcastlessInit ==
  /\ Init
  /\ (\A p \in correct : loc[p] = "idle")

\* nondeterministic reception of any subset of correct and byzantine messages
Receive(p, msgs) ==
  /\ loc[p] # "accept"
  /\ msgs \subseteq sent \cup ByzMsgs
  /\ recv' = [recv EXCEPT ![p] = msgs]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* a correct process that started with the broadcast accepts immediately
AcceptOnInit(p) ==
  /\ loc[p] = "broadcast"
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* the quiet case: just enough echoes to send, not yet enough to accept
EchoOnly(p) ==
  /\ loc[p] = "idle"
  /\ Cardinality(FromOf(recv[p] \cap EchoMsgs)) >= N - 2 * T
  /\ Cardinality(FromOf(recv[p] \cap EchoMsgs)) < N - T
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ loc' = [loc EXCEPT ![p] = "echoed"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* the loud case: enough echoes to send and accept
EchoAndAccept(p) ==
  /\ loc[p] = "idle"
  /\ Cardinality(FromOf(recv[p] \cap EchoMsgs)) >= N - T
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* once sent, a correct process still collecting echoes may accept late
AcceptLater(p) ==
  /\ loc[p] = "echoed"
  /\ Cardinality(FromOf(recv[p] \cap EchoMsgs)) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

\* weak fairness: a quiet correct process that can receive and act keeps doing so
Fairness ==
  \A p \in correct :
    /\ WF_vars(Receive(p, sent \cup ByzMsgs))
    /\ WF_vars(AcceptOnInit(p))
    /\ WF_vars(EchoOnly(p))
    /\ WF_vars(EchoAndAccept(p))
    /\ WF_vars(AcceptLater(p))

Next ==
  \/ \E p \in 1..N, msgs \in SUBSET AllMsgs : Receive(p, msgs)
  \/ \E p \in correct : AcceptOnInit(p)
  \/ \E p \in correct : EchoOnly(p)
  \/ \E p \in correct : EchoAndAccept(p)
  \/ \E p \in correct : AcceptLater(p)

\* the init-only branch (no broadcast) keeps running without fairness
InitOnlySpec == Init /\ [][Next]_vars

Spec == InitOnlySpec /\ Fairness

CorrLtl == (\A p \in correct : loc[p] = "broadcast") ~> (\A p \in correct : loc[p] = "accept")
RelayLtl == (\E p \in correct : loc[p] = "accept") ~> (\A p \in correct : loc[p] = "accept")
UnforgLtl == (\A p \in correct : loc[p] # "broadcast") ~> (\A p \in correct : loc[p] # "accept")

====