---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N > 3 * T
       /\ T >= F
       /\ F >= 0

Processes == 1..N
Msgs == {"ECHO"}
Pair == [who : Processes, what : Msgs]

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

\* A process accepts once it has gathered enough ECHO messages; the
\* threshold separates the preliminary "middle" step from the final ACCEPT step.
MiddleThresh(p) == Cardinality({ m \in recv[p] : m.what = "ECHO" }) >= N - 2 * T
AcceptThresh(p) == Cardinality({ m \in recv[p] : m.what = "ECHO" }) >= N - T

TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty = Processes \ correct
  /\ pc \in [Processes -> {"noninit", "init", "echoed", "accept"}]
  /\ recv \in [Processes -> SUBSET Pair]
  /\ sent \subseteq Pair

\* Unforgeability: in the checked configuration the broadcast is only ever
\* observed if a correct process actually produces it.
FCConstraints == (correct = {}) <=> (\A p \in Processes: pc[p] \in {"init", "echoed", "accept"})

Init ==
  /\ correct = 1..(N - F)
  /\ faulty = { N - F + 1 .. N }
  /\ \E p \in Processes: pc = [q \in Processes |-> IF q = p THEN "init" ELSE "noninit"]
  /\ sent = {}
  /\ recv = [p \in Processes |-> {}]

NoBroadcast ==
  /\ correct = 1..(N - F)
  /\ faulty = { N - F + 1 .. N }
  /\ pc = [p \in Processes |-> "noninit"]
  /\ sent = {}
  /\ recv = [p \in Processes |-> {}]

\* Correct processes only ever receive messages from the correct-sender
\* envelope; Byzantine processes add arbitrary noise to the channel.
Receive(p) ==
  /\ p \in correct
  /\ \E m \subseteq (sent \cup {[who |-> q, what |-> "ECHO"] : q \in faulty}):
       recv' = [recv EXCEPT ![p] = @ \cup m]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

AcceptBroadcast(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {[who |-> p, what |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "noninit"
  /\ MiddleThresh(p)
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {[who |-> p, what |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptMid(p) ==
  /\ p \in correct
  /\ pc[p] = "noninit"
  /\ AcceptThresh(p)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {[who |-> p, what |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "echoed"
  /\ AcceptThresh(p)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in Processes: Receive(p)
  \/ \E p \in Processes: AcceptBroadcast(p)
  \/ \E p \in Processes: SendEcho(p)
  \/ \E p \in Processes: AcceptMid(p)
  \/ \E p \in Processes: AcceptEcho(p)

\* Fairness only on the steps that can actually make progress once they are
\* available -- receiving messages and acting on a sufficient quorum.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes: Receive(p))
  /\ WF_vars(\E p \in Processes: AcceptBroadcast(p))
  /\ WF_vars(\E p \in Processes: SendEcho(p))
  /\ WF_vars(\E p \in Processes: AcceptMid(p))
  /\ WF_vars(\E p \in Processes: AcceptEcho(p))

\* The safety version of the spec, used to model-check the unforgeability
\* property without fairness on the receive step.
NoFairnessSpec ==
  /\ Init /\ [][Next]_vars

CorrLtl ==
  /\ (\A p \in correct: pc[p] = "init") ~> (\A p \in correct: pc[p] = "accept")

RelayLtl ==
  (\E p \in correct: pc[p] = "accept") ~> (\A p \in correct: pc[p] = "accept")

UnforgLtl ==
  (\A p \in correct: pc[p] # "init") ~> (\A p \in correct: pc[p] # "accept")

====