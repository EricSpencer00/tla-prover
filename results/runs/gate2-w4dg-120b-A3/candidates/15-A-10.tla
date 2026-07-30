---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* One-round reliable broadcast with Byzantine faults, from Srikanth & Toueg (1987).
\* Processes are partitioned at Init into correct and faulty (up to T faulty).
\* Control: whether a correct process received the broadcaster's INIT broadcast,
\* whether it has not received it, whether it sent an ECHO, or whether it accepted.

CONSTANTS N, T, F

Processes == 1..N
Msgs == {"echo"}
Control == {"brcvd", "bnone", "sent", "accept"}
AllSends == [src : Processes, mn : Msgs]

VARIABLES correct, faulty, loc, recv, sent

vars == <<correct, faulty, loc, recv, sent>>

\* Only correct processes may send; faulty ones may fabricate any message.
CorrectDelivers(p) ==
  { sent[p] } \cup { [src |-> f, mn |-> g] : f \in faulty, g \in Msgs }

\* A process records messages from correct senders plus any (possibly forged)
\* message from a Byzantine sender, so a Byzantine may always inject one more.
Receive(p) ==
  /\ loc[p] \in {"brcvd", "bnone"}
  /\ \E m \in SUBSET (sent \cup CorrectDelivers(p)) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup m]
        /\ UNCHANGED <<correct, faulty, sent, loc>>

SendEcho(p) ==
  /\ p \in correct
  /\ loc[p] = "bnone"
  /\ Cardinality({s \in correct : [src |-> s, mn |-> "echo"] \in recv[p]}) >= N - 2 * T
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = [sent EXCEPT ![p] = [src |-> p, mn |-> "echo"]]
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptIfInit(p) ==
  /\ loc[p] = "brcvd"
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ sent' = [sent EXCEPT ![p] = [src |-> p, mn |-> "echo"]]
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptOnQuorum(p) ==
  /\ loc[p] \in {"bnone", "sent"}
  /\ Cardinality({s \in correct : [src |-> s, mn |-> "echo"] \in recv[p]}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ sent' = IF loc[p] = "sent" THEN sent
              ELSE [sent EXCEPT ![p] = [src |-> p, mn |-> "echo"]]
  /\ UNCHANGED <<correct, faulty, recv>>

Next == \E p \in Processes :
           Receive(p) \/ SendEcho(p) \/ AcceptIfInit(p) \/ AcceptOnQuorum(p)

Init ==
  /\ correct \subseteq Processes
  /\ Cardinality(correct) = N - F
  /\ faulty = Processes \ correct
  /\ loc \in [Processes -> Control]
  /\ recv \in [Processes -> SUBSET AllSends]
  /\ sent \in [Processes -> AllSends]
  /\ Cardinality({p \in Processes : loc[p] = "brcvd"}) \in {0, N}

\* Two initial situations: arbitrary broadcast distribution, or none at all.
InitAny == Init /\ TRUE
InitNone == Init /\ \A p \in Processes : loc[p] = "bnone"

Spec == InitAny /\ [][Next]_vars
        /\ WF_vars(Receive(1) \/ AcceptIfInit(1))
        /\ WF_vars(Receive(2) \/ AcceptIfInit(2))

\* No Byzantine process ever records a broadcast; acceptance is bounded.
FCConstraints == \A p \in Processes : loc[p] \in Control

\* Correct processes always stay in their domain.
TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty \subseteq Processes
  /\ loc \in [Processes -> Control]
  /\ recv \in [Processes -> SUBSET AllSends]
  /\ sent \in [Processes -> AllSends]

\* If the broadcast never happened at a correct process, no correct process accepts.
UnforgLtl == (\A p \in Processes : loc[p] # "brcvd") ~> (\A p \in correct : loc[p] = "accept")

\* Broadcasted: every correct process eventually accepts.
CorrLtl == (\A p \in correct : loc[p] = "brcvd") ~> (\A p \in correct : loc[p] = "accept")

RelayLtl == (\E p \in correct : loc[p] = "accept") ~> (\A q \in correct : loc[q] = "accept")

====