---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

BcastMsg == "Bcast"
EchoMsg == "Echo"
Msgs == {BcastMsg, EchoMsg}
NONE == "None"

VARIABLES correct, faulty, pc, recvMsgs, sentMsgs

Vars == <<correct, faulty, pc, recvMsgs, sentMsgs>>

InitStates == {"nobc", "irecv"}

Nonsender(s) == {m \in recvMsgs[s] : m[2] = EchoMsg}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> InitStates \cup {"sent", "accept"}]
  /\ recvMsgs \in [1..N -> SUBSET (1..N \X Msgs)]
  /\ sentMsgs \subseteq (1..N \X Msgs)

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> InitStates]
  /\ recvMsgs = [s \in 1..N |-> {}]
  /\ sentMsgs = {}

InitNoBcast ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ pc = [s \in 1..N |-> "nobc"]
  /\ recvMsgs = [s \in 1..N |-> {}]
  /\ sentMsgs = {}

RECURSIVE MsgUnion(_, _)
MsgUnion(s, S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN recvMsgs[x][s] \cup MsgUnion(s, S \ {x})

RECURSIVE SentUnion(_)
SentUnion(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup SentUnion(S \ {x})

AllCorrectSent == SentUnion({s \in correct : pc[s] \in {"sent", "accept"}})

Receive(s, m) ==
  /\ s \in correct
  /\ m \in (AllCorrectSent \cup (faulty \X {EchoMsg}))
  /\ m \notin recvMsgs[s]
  /\ recvMsgs' = [recvMsgs EXCEPT ![s] = recvMsgs[s] \cup {m}]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

InitAccept(s) ==
  /\ s \in correct
  /\ pc[s] = "irecv"
  /\ sentMsgs' = sentMsgs \cup {<<s, BcastMsg>>}
  /\ pc' = [pc EXCEPT ![s] = "sent"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

EchoQuorum(s) ==
  /\ s \in correct
  /\ pc[s] # "accept"
  /\ Cardinality(Nonsender(s)) >= N - 2T
  /\ sentMsgs' = sentMsgs \cup {<<s, EchoMsg>>}
  /\ pc' = [pc EXCEPT ![s] = IF pc[s] = "irecv" THEN "sent" ELSE pc[s]]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

AcceptPhase(s) ==
  /\ s \in correct
  /\ pc[s] # "accept"
  /\ Cardinality(Nonsender(s)) >= N - T
  /\ sentMsgs' = sentMsgs \cup {<<s, EchoMsg>>}
  /\ pc' = [pc EXCEPT ![s] = "accept"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

RecvStep ==
  \/ \E s \in 1..N, m \in Msgs : Receive(s, <<s, m>>)
  \/ \E s \in 1..N : InitAccept(s)
  \/ \E s \in 1..N : EchoQuorum(s)
  \/ \E s \in 1..N : AcceptPhase(s)

Spec == Init /\ [][RecvStep]_Vars
        /\ WF_Vars(\E s \in 1..N, m \in Msgs : Receive(s, <<s, m>>))
        /\ WF_Vars(\E s \in 1..N : InitAccept(s))
        /\ WF_Vars(\E s \in 1..N : EchoQuorum(s))
        /\ WF_Vars(\E s \in 1..N : AcceptPhase(s))

FCConstraints == N > 3 * T

CorrLtl ==
  /\ \A s \in correct : pc[s] = "irecv"
  /\ (\E s \in correct : pc[s] = "accept") ~> (\A s \in correct : pc[s] = "accept")

RelayLtl ==
  (\E s \in correct : pc[s] = "accept") ~> (\A s \in correct : pc[s] = "accept")

UnforgLtl ==
  (\A s \in correct : pc[s] # "irecv") ~> (\A s \in correct : pc[s] # "accept")

====