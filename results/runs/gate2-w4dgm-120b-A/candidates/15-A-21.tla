---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, prog, recvMsgs, sentMsgs

vars == <<correct, faulty, prog, recvMsgs, sentMsgs>>

Procs == 0..(N - 1)
MessageTypes == {"ECHO"}
Senders == Procs \X MessageTypes
NoOne == <<N, "ECHO">>

ECHOes(p) == { m \in recvMsgs[p] : m[2] = "ECHO" }

TypeOK ==
  /\ correct \subseteq Procs
  /\ faulty \subseteq Procs
  /\ Cardinality(correct) = N - F
  /\ faulty = Procs \ correct
  /\ prog \in [Procs -> {"initrecv", "nobroadcast", "sent", "accepted"}]
  /\ recvMsgs \in [Procs -> SUBSET Senders]
  /\ sentMsgs \subseteq Senders

Init ==
  /\ correct = CHOOSE c \in { x \in SUBSET Procs : Cardinality(x) = N - F } :
                   TRUE
  /\ faulty = Procs \ correct
  /\ prog = [p \in Procs |-> IF p \in correct THEN "initrecv" ELSE "nobroadcast"]
  /\ recvMsgs = [p \in Procs |-> {}]
  /\ sentMsgs = {}

RestrictedInit ==
  /\ correct = CHOOSE c \in { x \in SUBSET Procs : Cardinality(x) = N - F } :
                   TRUE
  /\ faulty = Procs \ correct
  /\ prog = [p \in Procs |-> IF p \in correct THEN "nobroadcast" ELSE "initrecv"]
  /\ recvMsgs = [p \in Procs |-> {}]
  /\ sentMsgs = {}

Receive(p, m) ==
  /\ m \notin recvMsgs[p]
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup {m}]
  /\ UNCHANGED <<correct, faulty, prog, sentMsgs>>

ReceiveAny(p) ==
  \E m \in (sentMsgs \cup (faulty \X MessageTypes)) : Receive(p, m)

SendEcho(p) ==
  /\ prog[p] \in {"initrecv", "nobroadcast"}
  /\ prog' = [prog EXCEPT ![p] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

Accept(p) ==
  /\ prog[p] \in {"initrecv", "sent"}
  /\ prog' = [prog EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

InitAction == Init \/ RestrictedInit

ReceiveAction == \E p \in Procs : ReceiveAny(p)

SendAction == \E p \in Procs : SendEcho(p)

AcceptAction == \E p \in Procs : Accept(p)

Next == InitAction \/ ReceiveAction \/ SendAction \/ AcceptAction

InitA == Init \/ RestrictedInit

Spec == InitA /\ [][Next]_vars
        /\ WF_vars(ReceiveAction)
        /\ WF_vars(SendAction)
        /\ WF_vars(AcceptAction)

UnforgLtl == (\A p \in Procs : prog[p] = "nobroadcast")
              ~> (\A p \in Procs : prog[p] = "accepted")

CorrLtl == (\A p \in Procs : prog[p] = "initrecv")
              ~> (\A p \in Procs : prog[p] = "accepted")
RelayLtl == (\E p \in Procs : prog[p] = "accepted")
              ~> (\A p \in Procs : prog[p] = "accepted")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ correct = CHOOSE c \in { x \in SUBSET Procs : Cardinality(x) = N - F } :
                   TRUE
  /\ faulty = Procs \ correct

====