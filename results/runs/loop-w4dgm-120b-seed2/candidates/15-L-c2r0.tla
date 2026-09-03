---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recvMsgs, sentByCorrect

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"init","notinit","echoed","acc"}]
  /\ recvMsgs \in [1..N -> SUBSET (1..N \X {"echo"})]
  /\ sentByCorrect \subseteq (1..N)

Init ==
  /\ correct = (1..N) \ {N-F+1..N}
  /\ faulty = 1..N \ correct
  /\ pc = [p \in 1..N |-> IF p \in correct THEN "init" ELSE "notinit"]
  /\ recvMsgs = [p \in 1..N |-> {}]
  /\ sentByCorrect = {}

NoInit ==
  /\ correct \subseteq {p \in 1..N : pc[p] = "notinit"}
  /\ sentByCorrect = {}

AllCorrectInit ==
  /\ correct \subseteq {p \in 1..N : pc[p] = "init"}
  /\ sentByCorrect = {}

NoInitCrashed ==
  /\ \A p \in correct : pc[p] # "acc"
  /\ sentByCorrect = {}

InitCrashed ==
  /\ \A p \in correct : pc[p] = "acc"
  /\ sentByCorrect = {}

RECURSIVE MsgSetOf(_)
MsgSetOf(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN
       (1..N \X {"echo"}) \cup MsgSetOf(S \ {x})

SentByCorrect == MsgSetOf(sentByCorrect)

RECURSIVE SendersE(_)
SendersE(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x[1]} \cup SendersE(S \ {x})

ReceiveMsgs(p, m) ==
  /\ p \in correct
  /\ m # {}
  /\ m \subseteq sentByCorrect \cup {x \in 1..N \X {"echo"} : x[1] \in faulty}
  /\ m \cap recvMsgs[p] = {}
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup m]
  /\ UNCHANGED <<correct, faulty, pc, sentByCorrect>>

InitAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ sentByCorrect' = sentByCorrect \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

EchoWithoutAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "notinit"
  /\ Cardinality(SendersE(recvMsgs[p])) >= N - 2 * T
  /\ Cardinality(SendersE(recvMsgs[p])) < N - T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sentByCorrect' = sentByCorrect \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

EchoAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "notinit"
  /\ Cardinality(SendersE(recvMsgs[p])) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ sentByCorrect' = sentByCorrect \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

LateAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "echoed"
  /\ Cardinality(SendersE(recvMsgs[p])) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentByCorrect>>

Next ==
  \/ \E p \in 1..N, m \in SUBSET (1..N \X {"echo"}) : ReceiveMsgs(p, m)
  \/ \E p \in 1..N : InitAccept(p) \/ EchoWithoutAccept(p) \/ EchoAndAccept(p) \/ LateAccept(p)

Spec == Init /\ [][Next]_<<correct, faulty, pc, recvMsgs, sentByCorrect>>
  /\ (\A p \in 1..N : WF_vars(ReceiveMsgs(p, sentByCorrect \cup {x \in 1..N \X {"echo"} : x[1] \in faulty})))

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

CorrLtl == AllCorrectInit ~> InitCrashed
RelayLtl == NoInitCrashed ~> InitCrashed
UnforgLtl == NoInit ~> InitCrashed

====