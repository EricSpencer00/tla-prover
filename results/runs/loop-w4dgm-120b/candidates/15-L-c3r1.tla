---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

\* Protocol from Srikanth and Toueg 1987 Figure 7: a correct process accepts
\* once it has collected >= N - T ECHO messages. Byzantine processes may
\* forge ECHO messages arbitrarily, so unforgeability must rest on the
\* fact that no correct process accepts when none broadcasts.

VARIABLES correct, faulty, pc, recvd, sent

vars == <<correct, faulty, pc, recvd, sent>>

Procs == 0..(N - 1)
Msg == [sg: Procs, tp: {"ECHO"}]

NMinusT == N - T
NMinus2T == N - 2 * T

InitState(p) == IF p < (N - F) THEN "hasinit" ELSE "noinit"

EchoCount(p) == Cardinality({m \in recvd[p] : m.tp = "ECHO"})
DistinctSenders(p) == {m.sg : m \in recvd[p]}

TypeOK ==
  /\ correct \subseteq Procs
  /\ faulty \subseteq Procs
  /\ pc \in [Procs -> {"hasinit", "noinit", "sent", "accept"}]
  /\ recvd \in [Procs -> SUBSET Msg]
  /\ sent \subseteq Msg

\* Unforgeability holds regardless of fairness: if no correct process
\* broadcasts (all start in the non-broadcast state), none can ever
\* collect enough ECHO messages to accept.
FCConstraints ==
  \A p \in Procs : InitState(p) = "noinit" => pc[p] # "accept"

Init ==
  /\ correct = 0..(N - F - 1)
  /\ faulty = (N - F)..(N - 1)
  /\ pc = [p \in Procs |-> InitState(p)]
  /\ recvd = [p \in Procs |-> {}]
  /\ sent = {}

Nxt(p) == IF p = N - 1 THEN 0 ELSE p + 1

\* RECEIVE combines every ECHO that a correct sender has already sent with
\* arbitrary ECHO messages from Byzantine processes, so it is never stuck
\* waiting on a slow (but correct) process.
Receive(p) ==
  /\ sent # {}
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup (sent \cup
       { [sg |-> q, tp |-> "ECHO"] : q \in faulty })]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

Broadcast(p) ==
  /\ pc[p] = "hasinit"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [sg |-> p, tp |-> "ECHO"] }
  /\ UNCHANGED <<correct, faulty, recvd>>

Relay(p) ==
  /\ pc[p] = "noinit"
  /\ EchoCount(p) >= NMinus2T
  /\ EchoCount(p) < NMinusT
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup { [sg |-> p, tp |-> "ECHO"] }
  /\ UNCHANGED <<correct, faulty, recvd>>

RelayStrong(p) ==
  /\ pc[p] = "noinit"
  /\ EchoCount(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup { [sg |-> p, tp |-> "ECHO"] }
  /\ UNCHANGED <<correct, faulty, recvd>>

RelayComplete(p) ==
  /\ pc[p] = "sent"
  /\ EchoCount(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recvd, sent>>

Next ==
  \/ \E p \in Procs : Receive(p)
  \/ \E p \in Procs : Broadcast(p)
  \/ \E p \in Procs : Relay(p)
  \/ \E p \in Procs : RelayStrong(p)
  \/ \E p \in Procs : RelayComplete(p)

Spec == Init /\ [][Next]_vars
    /\ (\A p \in Procs : WF_vars(Receive(p)))
    /\ (\A p \in Procs : WF_vars(Broadcast(p)))
    /\ (\A p \in Procs : WF_vars(Relay(p)))
    /\ (\A p \in Procs : WF_vars(RelayStrong(p)))
    /\ (\A p \in Procs : WF_vars(RelayComplete(p)))

CorrLtl == (\A p \in correct : pc[p] = "hasinit") ~> (\A p \in correct : pc[p] = "accept")
RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")
UnforgLtl == (\A p \in Procs : InitState(p) = "noinit") ~> (\A p \in Procs : pc[p] # "accept")

====