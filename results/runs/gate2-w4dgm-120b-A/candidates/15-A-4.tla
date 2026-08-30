---- MODULE bcastByz ----
\* Reliable broadcast with Byzantine faults, based on Srikanth and Toueg 1987 figure 7.
\* The INIT message is modeled as an initial value per process rather than a separate
\* sender, so the "sent" set only ever grows ECHO messages and unforgeability is about
\* not fabricating an acceptance without a genuine INIT.
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME N > 3 * T
ASSUME T >= F

Msg == [from: 1..N, kind: {"ECHO"}]

VARIABLES correct, faulty, pc, recvMsgs, sent

vars == <<correct, faulty, pc, recvMsgs, sent>>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"init", "none", "sent", "accept"}]
  /\ recvMsgs \in [1..N -> SUBSET Msg]
  /\ sent \subseteq Msg

Init ==
  /\ correct = {1..N \ F}
  /\ faulty = {1..N} \ correct
  /\ pc \in {<<init, "none">>, <<"none", "init">>}
  /\ recvMsgs = [p \in 1..N |-> {}]
  /\ sent = {}

\* Second initial state: no correct process ever broadcasts.
HushInit ==
  /\ correct = {1..N \ F}
  /\ faulty = {1..N} \ correct
  /\ pc = [p \in 1..N |-> "none"]
  /\ recvMsgs = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process receives any subset of what correct processes have sent plus
\* arbitrary Byzantine chatter (the Byzantine-capable "receive any" style).
Receive(p) ==
  /\ p \in correct
  /\ pc[p] \in {"init", "none"}
  /\ \E S \in SUBSET (sent \cup { [from |-> q, kind |-> "ECHO"] : q \in faulty }):
       recvMsgs' = [recvMsgs EXCEPT ![p] = @ \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

BroadcastInit(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [from |-> p, kind |-> "ECHO"] }
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] = @ \cup { [from |-> p, kind |-> "ECHO"] }]
  /\ UNCHANGED <<correct, faulty>>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "none"
  /\ Cardinality({m \in recvMsgs[p] : m.kind = "ECHO"}) >= N - 2 * T
  /\ Cardinality({m \in recvMsgs[p] : m.kind = "ECHO"}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup { [from |-> p, kind |-> "ECHO"] }
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] = @ \cup { [from |-> p, kind |-> "ECHO"] }]
  /\ UNCHANGED <<correct, faulty>>

Accept(p) ==
  /\ p \in correct
  /\ pc[p] \in {"none", "sent"}
  /\ Cardinality({m \in recvMsgs[p] : m.kind = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [from |-> p, kind |-> "ECHO"] }
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] = @ \cup { [from |-> p, kind |-> "ECHO"] }]
  /\ UNCHANGED <<correct, faulty>>

Next ==
  \/ \E p \in 1..N: Receive(p)
  \/ \E p \in 1..N: BroadcastInit(p)
  \/ \E p \in 1..N: SendEcho(p)
  \/ \E p \in 1..N: Accept(p)

\* Receive-and-act steps of correct processes are weakly fair together, so if a
\* correct process can always keep receiving messages from correct ECHOers it does.
Spec == Init /\ [][Next]_vars /\ WF_vars(Receive(1)) /\ WF_vars(Receive(2))
                            /\ WF_vars(Receive(3)) /\ WF_vars(Receive(4))

CorrLtl == (\A p \in correct: pc[p] = "init") ~> (\A p \in correct: pc[p] = "accept")
RelayLtl == (\E p \in correct: pc[p] = "accept") ~> (\A p \in correct: pc[p] = "accept")
UnforgLtl == (\A p \in correct: pc[p] # "init") ~> (\A p \in correct: pc[p] # "accept")

FCConstraints == WF_vars(Receive(1)) /\ WF_vars(Receive(2))
                 /\ WF_vars(Receive(3)) /\ WF_vars(Receive(4))

====