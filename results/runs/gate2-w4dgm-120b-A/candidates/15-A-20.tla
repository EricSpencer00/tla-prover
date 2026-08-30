---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sentMsgs
vars == <<correct, faulty, pc, recv, sentMsgs>>

Procs == 0..(N - 1)
Msgs == {"echo"}
InitMsgs(p) == IF p \in correct THEN {"init"} ELSE {}
MaxMsgs == 2 * N

CONTROL == {"initstate", "nonstate", "sentEcho", "accepted"}

\* A correct process accepts on seeing a quorum of ECHO messages from
\* distinct senders; this is what makes the broadcast reliable.
Quorum(p) == Cardinality({q \in correct : [id |-> q, typ |-> "echo"] \in recv[p]})

Init ==
  /\ \E group \in {correct : Cardinality(correct) = N - F /\ faulty = Procs \ correct : TRUE}
  /\ \E r \in {0, 1} :
       pc = [p \in Procs |-> IF r = 1 /\ p \in correct THEN "initstate" ELSE "nonstate"]
  /\ recv = [p \in Procs |-> InitMsgs(p)]
  /\ sentMsgs = {}

\* A correct process may absorb any fresh messages presented to it, from
\* correct senders or from the Byzantine complement.
Receive(p) ==
  \E newMsgs \in SUBSET (sentMsgs \cup { [id |-> q, typ |-> "echo"] : q \in Procs }) :
    /\ ~ \E m \in newMsgs : m \in recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

SendEcho(p) ==
  /\ pc[p] \in {"initstate", "nonstate"}
  /\ sentMsgs' = sentMsgs \cup {[id |-> p, typ |-> "echo"]}
  /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ UNCHANGED <<correct, faulty, recv>>

Accept(p) ==
  /\ pc[p] \in {"initstate", "nonstate", "sentEcho"}
  /\ Quorum(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sentMsgs>>

Next == \E p \in Procs : Receive(p) \/ SendEcho(p) \/ Accept(p)

TypeOK ==
  /\ correct \subseteq Procs
  /\ pc \in [Procs -> CONTROL]
  /\ recv \in [Procs -> SUBSET [id : Procs, typ : { "init", "echo" }]]
  /\ sentMsgs \subseteq [id : Procs, typ : { "echo" }]
  /\ N \in Nat /\ T \in Nat /\ F \in Nat

\* Unforgeability: if no correct process got the INIT broadcast, none
\* accepts. Correctness: if every correct process got it, they all accept.
CorrLtl == (\A p \in correct : pc[p] = "initstate") ~> (\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")
UnforgLtl == (\A p \in correct : pc[p] \in {"nonstate", "sentEcho"}) ~> (\A p \in correct : pc[p] \in {"nonstate", "sentEcho"})

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = N - F

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Procs : Receive(p))
  /\ WF_vars(\E p \in Procs : SendEcho(p))
  /\ WF_vars(\E p \in Procs : Accept(p))
  /\ FCConstraints
====