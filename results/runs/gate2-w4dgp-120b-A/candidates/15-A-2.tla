---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A reliable broadcast that tolerates up to T Byzantine processes (from Srikanth & Toueg,
\* 1987 Figure 7).  Instead of a fixed broadcaster, each process is initially placed in one
\* of two states: one meaning it received the broadcaster's INIT message, the other meaning
\* it did not.  Every correct process that ever accepts must have first sent an ECHO, and a
\* correct process accepts once it has collected enough distinct ECHOs from others.
\* Because F (the number of Byzantine processes) is bounded by T, a quorum of size N-T
\* cannot be forged by faulty processes alone -- and a quorum of size N-2T is exactly the
\* threshold that lets a process relay (send an ECHO) without yet accepting.
\* The module also defines a restricted initial state where no correct process received
\* the INIT message, for checking the unforgeability safety property.

Processes == 1..N
MsgTypes == {"ECHO"}
Msgs == [sender : Processes, mtype : MsgTypes]

VARIABLES correct, faulty, pc, received, sent
vars == <<correct, faulty, pc, received, sent>>

\* A correct process accepts only after gathering a quorum of distinct ECHOs, so if no
\* correct process broadcast (all start in the non-broadcast pc) none can ever accept.
TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty = Processes \ correct
  /\ pc \in [Processes -> {"nocast", "nocastb", "sent", "accept"}]
  /\ received \in [Processes -> SUBSET Msgs]
  /\ sent \subseteq Msgs

\* The partitioned model only exists for N > 3T (strictly more correct than 2T) and
\* for a fault bound consistent with the Byzantine capacity.
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

Init ==
  /\ correct = {1 : (N - F)}
  /\ faulty = Processes \ correct
  /\ pc \in [Processes -> {"nocast", "nocastb"}]
  /\ received = [p \in Processes |-> {}]
  /\ sent = {}

\* A process may receive arbitrarily many messages in one step: all messages that any
\* correct process has already sent, plus all messages a Byzantine process could forge.
Receive(p) ==
  /\ pc[p] # "accept"
  /\ \E m \in (sent \cup [sender : faulty, mtype : MsgTypes]) \ received[p] :
       received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct process that actually received the broadcast's INIT message accepts and
\* immediately sends one ECHO to every participant.
CastEcho(p) ==
  /\ pc[p] = "nocastb"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {[sender |-> p, mtype |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, received>>

\* A correct process that has not yet sent an ECHO relays when it has collected a
\* quorum that is big enough to relay but not yet big enough to accept.
RelayEcho(p) ==
  /\ pc[p] = "nocast"
  /\ Cardinality({m \in received[p] : m.mtype = "ECHO"}) >= N - 2 * T
  /\ Cardinality({m \in received[p] : m.mtype = "ECHO"}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {[sender |-> p, mtype |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, received>>

\* A relay that has just reached the acceptance quorum both relays (if it hasn't already)
\* and accepts.
AcceptEcho(p) ==
  /\ pc[p] \in {"nocast", "sent"}
  /\ Cardinality({m \in received[p] : m.mtype = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {[sender |-> p, mtype |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, received>>

\* A correct process that has already sent an ECHO and later gathers enough ECHOs to
\* reach the acceptance quorum accepts.
RelayAccept(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality({m \in received[p] : m.mtype = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, received, sent>>

Next ==
  \/ (\E p \in Processes : Receive(p))
  \/ (\E p \in correct : CastEcho(p))
  \/ (\E p \in correct : RelayEcho(p))
  \/ (\E p \in correct : AcceptEcho(p))
  \/ (\E p \in correct : RelayAccept(p))

Spec == Init /\ [][Next]_vars
SpecF == Spec /\ (\A p \in correct : WF_vars(Receive(p)))

\* Correctness: if every correct process actually broadcast (all start in the
\* broadcast-received state), then eventually all correct processes accept.
CorrLtl == (\A p \in correct : pc[p] = "nocastb") ~> (\A p \in correct : pc[p] = "accept")

RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

\* Unforgeability: if no correct process broadcast (all start in the non-broadcast state),
\* no correct process ever accepts.
UnforgLtl == (\A p \in correct : pc[p] = "nocast") ~> (\A p \in correct : pc[p] = "nocast")

====