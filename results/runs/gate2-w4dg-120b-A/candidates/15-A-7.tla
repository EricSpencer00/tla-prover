---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Partition of processes; the correct set is chosen at Init and thereafter
\* is immutable -- its size is fixed as N-F by the model's constants.
\* A process starts either having heard the broadcaster's INIT message
\* or not, which replaces a dedicated sender in this formulation.
\* The state machine is exactly the one-round ST87B protocol.
\* N > 3T is the integrity bound; T >= F is the Byzantine bound.
\* The module exports every identifier the reference .cfg expects.

Processes == 1..N
MsgTypes == {"ECHO"}
Msgs == [frm : Processes, typ : MsgTypes]

VARIABLES correct, faulty, pc, inbox, sent

vars == <<correct, faulty, pc, inbox, sent>>

TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty = Processes \ correct
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ pc \in [Processes -> {"noinit", "init", "sent", "accept"}]
  /\ inbox \in [Processes -> SUBSET Msgs]
  /\ sent \subseteq Msgs

FCConstraints == Cardinality(correct) # 0

Init ==
  /\ \E g \in [Processes -> {"init", "noinit"}] :
       correct = {p \in Processes : g[p] = "init"}
  /\ faulty = Processes \ correct
  /\ pc = [p \in Processes |-> g[p]]
  /\ inbox = [p \in Processes |-> {}]
  /\ sent = {}

\* A correct process is always eligible to receive any set of new messages
\* that correct processes ever sent, plus arbitrary Byzantine ones.
Receipt(p, S) ==
  /\ pc[p] \in {"init", "sent", "accept"}
  /\ S \subseteq sent \cup [frm |-> 1..N, typ |-> "ECHO"]
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A gossip-initiated accept: an INIT keeps if the process agreed immediately.
Initiate(p) ==
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {[frm |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* Relaying on the short side: just enough votes to send, not to accept.
RelayLow(p) ==
  /\ pc[p] = "noinit"
  /\ Cardinality({m \in inbox[p] : m.typ = "ECHO"}) >= N - 2 * T
  /\ Cardinality({m \in inbox[p] : m.typ = "ECHO"}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {[frm |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* Relaying on the long side: enough votes to send and accept together.
RelayHigh(p) ==
  /\ pc[p] = "noinit"
  /\ Cardinality({m \in inbox[p] : m.typ = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {[frm |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A late accept after the ECHO was already sent on the short side.
LateAccept(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality({m \in inbox[p] : m.typ = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

Receivers == {p \in Processes : \E S \in SUBSET Msgs : Receipt(p, S)}
RelayersL == {p \in Processes : RelayLow(p)}
RelayersH == {p \in Processes : RelayHigh(p)}
Accpters == {p \in Processes : LateAccept(p)}
Initers == {p \in Processes : Initiate(p)}

Next ==
  \/ \E p \in Processes : Receipt(p, {})
  \/ \E p \in Processes : Initiate(p)
  \/ \E p \in Processes : RelayLow(p)
  \/ \E p \in Processes : RelayHigh(p)
  \/ \E p \in Processes : LateAccept(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Receivers)
  /\ WF_vars(RelayersL)
  /\ WF_vars(RelayersH)
  /\ WF_vars(Accpters)
  /\ WF_vars(Initers)

CorrLtl == \A p \in correct : (pc[p] = "init") ~> (pc[p] = "accept")
RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")
UnforgLtl == (\A p \in correct : pc[p] = "noinit") ~> (\A p \in correct : pc[p] # "accept")

====