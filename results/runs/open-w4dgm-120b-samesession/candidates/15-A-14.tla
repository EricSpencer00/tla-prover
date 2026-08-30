---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Strictly more than 2T correct processes participate in relay, so the
\* two acceptance thresholds (N-2T and N-T) cannot both be reachable by
\* tampering with the messages that correct processes actually send.
\* F is the number of Byzantine processes that may send arbitrary messages.

\* pc = "none" : has not received the broadcaster's INIT message.
\* pc = "hasinit" : received the broadcaster's INIT message.
\* pc = "sent" : already sent an ECHO message to everyone.
\* pc = "accepted" : has already accepted the broadcast.
Nodes == 1..N
Types == {"none", "hasinit", "sent", "accepted"}
Msgs == [node : Nodes, kind : {"init", "echo"}]
SentBy(k) == {m.node : m \in {x \in sentMsgs : x.node = k}}
EchoSenders(n) == {m.node : m \in {x \in rcvdMsgs[n] : x.kind = "echo"}}

VARIABLES correct, faulty, pc, rcvdMsgs, sentMsgs

vars == <<correct, faulty, pc, rcvdMsgs, sentMsgs>>

TypeOK ==
  /\ correct \subseteq Nodes
  /\ faulty \subseteq Nodes
  /\ pc \in [Nodes -> Types]
  /\ rcvdMsgs \in [Nodes -> SUBSET Msgs]
  /\ sentMsgs \subseteq Msgs

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = Nodes \ correct
  /\ sentMsgs = {}
  /\ \E pc0 \in [Nodes -> {"none", "hasinit"}]:
       /\ pc = pc0
       /\ \A n \in Nodes: pc[n] = "hasinit" => n \in correct
  /\ rcvdMsgs = [n \in Nodes |-> {}]

InitRestricted ==
  /\ sentMsgs = {}
  /\ \A n \in Nodes: pc[n] = "none"
  /\ correct = Nodes \ {N}
  /\ faulty = {N}

\* Execution is driven by the correct processes only: they are the only
\* ones that receive messages from correct senders and act on them.
Receive(n, kind) ==
  /\ n \in correct
  /\ pc[n] # "accepted"
  /\ kind \in {"init", "echo"}
  /\ rcvdMsgs' = [rcvdMsgs EXCEPT ![n] = rcvdMsgs[n] \cup
                                    {m \in sentMsgs : m.kind = kind}]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

SendInit(n) ==
  /\ n \in correct
  /\ pc[n] = "hasinit"
  /\ pc' = [pc EXCEPT ![n] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {[node |-> n, kind |-> "init"]}
  /\ UNCHANGED <<correct, faulty, rcvdMsgs>>

SendEcho(n) ==
  /\ n \in correct
  /\ pc[n] # "sent"
  /\ Cardinality(EchoSenders(n)) >= N - 2T
  /\ pc' = [pc EXCEPT ![n] = "sent"]
  /\ sentMsgs' = sentMsgs \cup
       {[node |-> n, kind |-> "echo"] : m \in sentMsgs, m.kind = "init"}
  /\ UNCHANGED <<correct, faulty, rcvdMsgs>>

ActOnEcho(n) ==
  /\ n \in correct
  /\ pc[n] = "sent"
  /\ Cardinality(EchoSenders(n)) >= N - T
  /\ pc' = [pc EXCEPT ![n] = "accepted"]
  /\ UNCHANGED <<correct, faulty, rcvdMsgs, sentMsgs>>

Next ==
  \/ \E n \in Nodes, k \in {"init", "echo"}: Receive(n, k)
  \/ \E n \in Nodes: SendInit(n) \/ SendEcho(n) \/ ActOnEcho(n)

Spec == Init /\ [][Next]_vars
    /\ \A n \in Nodes:
         /\ SF_vars(Receive(n, "init")) /\ SF_vars(Receive(n, "echo"))
         /\ SF_vars(SendEcho(n)) /\ SF_vars(ActOnEcho(n))

\* Safety: if the broadcaster never reaches a correct process, no correct
\* process may ever accept the broadcast it never saw.
Unforgeable == (\A n \in correct: pc[n] # "hasinit") => (\A n \in correct: pc[n] # "accepted")

FCConstraints == N > 3 * T

CorrLtl == <>(\A n \in correct: pc[n] = "accepted")
RelayLtl == (\E n \in correct: pc[n] = "accepted") ~> (\A n \in correct: pc[n] = "accepted")
UnforgLtl == []FCConstraints /\ []Unforgeable

====