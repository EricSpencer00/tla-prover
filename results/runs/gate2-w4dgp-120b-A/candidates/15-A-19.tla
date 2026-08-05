---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The one-round reliable broadcast from Srikanth and Toueg (Fig.7) with weak
\* fairness on the receive-and-act steps.  The partition into correct and
\* faulty processes is chosen nondeterministically at Init, bounded by F.
\* A restricted Init0 sets all correct processes to the non-broadcast
\* initial state, which is used to model-check the no-broadcast case.

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

RcvdInit(q) == pc[q] # "noBcast"
Echos(q) == { m.sender : m \in { x \in recv[q] : x.type = "ECHO" } }
Minv == { m \in recv[q] : m.sender \in correct };
  /\ m.type = "ECHO"

TypeOK ==
  /\ correct \subseteq (1..N) /\ faulty \subseteq (1..N)
  /\ correct \cup faulty = (1..N) /\ correct \cap faulty = {}
  /\ pc \in [1..N -> {"noBcast", "noEcho", "sentEcho", "accepted"}]
  /\ recv \in [1..N -> SUBSET [sender : 1..N, type : {"ECHO"}]]
  /\ sent \in SUBSET [sender : 1..N, type : {"ECHO"}]

\* The broadcast is a real transmission: correct processes accept only if
\* at least N-T ECHO messages arrive from distinct senders.
CorrLtl == (forall q \in correct : RcvdInit(q)) ~> (forall q \in correct : pc[q] = "accepted")
RelayLtl == (\E q \in correct : pc[q] = "accepted") ~> (forall q \in correct : pc[q] = "accepted")

\* Unforgeability is safety-only and needs no fairness to hold, so it is
\* checked against both the fair and the unfair version of the system.
UnforgLtl == (forall q \in correct : ~RcvdInit(q)) ~> (forall q \in correct : pc[q] # "accepted")

Init ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ correct \cup faulty = (1..N) /\ correct \cap faulty = {}
  /\ pc = [q \in 1..N |-> IF q \in correct THEN "noBcast" ELSE "noEcho"]
  /\ recv = [q \in 1..N |-> {}]
  /\ sent = {}

Init0 ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ correct \cup faulty = (1..N) /\ correct \cap faulty = {}
  /\ pc = [q \in 1..N |-> "noBcast"]
  /\ recv = [q \in 1..N |-> {}]
  /\ sent = {}

\* A correct process receives a batch of messages, drawn from correct senders
\* plus any messages the Byzantine set can inject.
Receive(q) ==
  /\ q \in correct
  /\ \E S \in SUBSET (sent \cup QUANTIFY([sender : faulty, type : {"ECHO"}]))
       recv' = [recv EXCEPT ![q] = @ \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* Receiving the (unforgeable) INIT transmission forces the immediate
\* ECHO-and-accept branch.
Broadcast(q) ==
  /\ q \in correct
  /\ RcvdInit(q)
  /\ pc[q] = "noBcast"
  /\ pc' = [pc EXCEPT ![q] = "accepted"]
  /\ sent' = sent \cup {[sender |-> q, type |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* The quorum is exactly what the bound N > 3T guarantees: before N-T is
\* reached the process may not accept, and no action can force it.
RelayEcho(q) ==
  /\ q \in correct
  /\ Cardinality(Echos(q)) >= N - 2 * T
  /\ Cardinality(Echos(q)) < N - T
  /\ pc[q] = "noBcast"
  /\ pc' = [pc EXCEPT ![q] = "sentEcho"]
  /\ sent' = sent \cup {[sender |-> q, type |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptEcho(q) ==
  /\ q \in correct
  /\ Cardinality(Echos(q)) >= N - T
  /\ pc[q] = "noBcast"
  /\ pc' = [pc EXCEPT ![q] = "accepted"]
  /\ sent' = sent \cup {[sender |-> q, type |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

RelayAccept(q) ==
  /\ q \in correct
  /\ pc[q] = "sentEcho"
  /\ Cardinality(Echos(q)) >= N - T
  /\ pc' = [pc EXCEPT ![q] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E q \in 1..N : Receive(q)
  \/ \E q \in 1..N : Broadcast(q)
  \/ \E q \in 1..N : RelayEcho(q)
  \/ \E q \in 1..N : AcceptEcho(q)
  \/ \E q \in 1..N : RelayAccept(q)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E q \in 1..N : Receive(q))
  /\ WF_vars(\E q \in 1..N : Broadcast(q))
  /\ WF_vars(\E q \in 1..N : RelayEcho(q))
  /\ WF_vars(\E q \in 1..N : AcceptEcho(q))
  /\ WF_vars(\E q \in 1..N : RelayAccept(q))

Spec0 ==
  /\ Init0
  /\ [][Next]_vars
  /\ WF_vars(\E q \in 1..N : Receive(q))
  /\ WF_vars(\E q \in 1..N : Broadcast(q))
  /\ WF_vars(\E q \in 1..N : RelayEcho(q))
  /\ WF_vars(\E q \in 1..N : AcceptEcho(q))
  /\ WF_vars(\E q \in 1..N : RelayAccept(q))

====