---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Initial broadcast-state: whether the broadcaster's INIT message was seen.
\* A restricted start is the no-broadcast case (no correct node sees INIT).
VARIABLES correct, faulty, pc, inbox, sent

Vars == <<correct, faulty, pc, inbox, sent>>

Nodes == 1..N
MessageTypes == {"ECHO"}
Msgs == Nodes \X MessageTypes
Quorum(Nt, t) == Nt - t

TypeOK ==
  /\ correct \subseteq Nodes
  /\ faulty \subseteq Nodes
  /\ correct \cap faulty = {}
  /\ pc \in [Nodes -> {"hasInit", "noInit", "sentEcho", "accepted"}]
  /\ inbox \in [Nodes -> SUBSET Msgs]
  /\ sent \subseteq Msgs

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ \A n \in Nodes : pc[n] \in {"hasInit", "noInit", "sentEcho", "accepted"}
  /\ \A n \in Nodes : inbox[n] \subseteq Msgs
  /\ \A n \in Nodes : sent \subseteq Msgs

Init ==
  /\ correct = {n \in Nodes : n <= N - F}
  /\ faulty = Nodes \ correct
  /\ pc \in [Nodes -> {"hasInit", "noInit", "sentEcho", "accepted"}]
  /\ inbox = [n \in Nodes |-> {}]
  /\ sent = {}

\* A correct node may receive any batch of new messages (its own + Byzantine).
Receive(n, mw) ==
  /\ n \in correct
  /\ pc[n] # "accepted"
  /\ inbox' = [inbox EXCEPT ![n] = inbox[n] \cup mw]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(n) ==
  /\ n \in correct
  /\ pc[n] # "accepted"
  /\ sent' = sent \cup {<<n, "ECHO">>}
  /\ pc' = [pc EXCEPT ![n] = "sentEcho"]
  /\ UNCHANGED <<correct, faulty, inbox>>

Accept(n) ==
  /\ n \in correct
  /\ pc[n] # "accepted"
  /\ pc' = [pc EXCEPT ![n] = "accepted"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

InitAccept(n) ==
  /\ n \in correct
  /\ pc[n] = "hasInit"
  /\ SendEcho(n) /\ Accept(n)

\* Bounded capacity: the two thresholds are distinct windows of ECHO count.
\* The lower window lets a node echo early without yet accepting.
BoundedEcho(n) ==
  /\ n \in correct
  /\ pc[n] = "noInit"
  /\ Cardinality(inbox[n]) >= Quorum(N, 2 * T)
  /\ Cardinality(inbox[n]) < Quorum(N, T)
  /\ SendEcho(n)

TallyEcho(n) ==
  /\ n \in correct
  /\ pc[n] = "noInit"
  /\ Cardinality(inbox[n]) >= Quorum(N, T)
  /\ SendEcho(n) /\ Accept(n)

EchoTally(n) == SendEcho(n) /\ Accept(n)

Next ==
  \/ \E n \in Nodes : InitAccept(n) \/ BoundedEcho(n) \/ TallyEcho(n)
  \/ \E n \in Nodes, mw \in SUBSET Msgs : Receive(n, mw)
  \/ \E n \in Nodes : EchoTally(n)

\* FAIRNESS: weak fairness on the combined receive-and-act steps of a correct
\* node -- needed for the liveness properties, not for safety (unforgeability).
Spec == Init /\ [][Next]_Vars
  /\ \A n \in Nodes :
       /\ TRUE
       /\ WF_Vars(\E mw \in SUBSET Msgs : Receive(n, mw))
       /\ WF_Vars(EchoTally(n))

UnforgLtl ==
  \A n \in Nodes : (n \in correct) => (pc[n] # "accepted" U (pc[n] = "accepted"))
  /\ ~( \A n \in correct : pc[n] = "noInit" )
  /\ ( \A n \in correct : pc[n] = "noInit" ) ~> ( \A n \in correct : pc[n] = "accepted" )
  /\ ( \E n \in Nodes : pc[n] = "accepted" ) ~> ( \A n \in correct : pc[n] = "accepted" )

CorrLtl == (\A n \in correct : pc[n] = "hasInit") ~> (\A n \in correct : pc[n] = "accepted")
RelayLtl == (\E n \in Nodes : pc[n] = "accepted") ~> (\A n \in correct : pc[n] = "accepted")

====