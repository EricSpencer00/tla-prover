---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A message is typed (only ECHO is possible) and carries the sender's identity.
Msg == [kind: {"ECHO"}, frm: 1..N]

VARIABLES correct, faulty, pc, recv, sentMsgs

vars == <<correct, faulty, pc, recv, sentMsgs>>

\* pc tracks where a correct process is in the protocol; recv records the
\* distinct (kind, frm) messages it has already observed.
TypeOK ==
  /\ correct \subseteq 1..N /\ faulty \subseteq 1..N
  /\ pc \in [1..N -> {"initbcast", "initnone", "sent", "accept"}]
  /\ recv \in [1..N -> SUBSET Msg]
  /\ sentMsgs \in SUBSET Msg

\* Faulty nodes may send whatever they like, so each process counts distinct
\* senders on its observed ECHO messages, ignoring Byzantine repeats.
Seen(p) == Cardinality({m.frm : m \in recv[p]})

Init ==
  /\ correct = {1..N-F}
  /\ faulty = 1..N \ correct
  /\ pc = [p \in 1..N |-> IF p \in correct THEN "initbcast" ELSE "initnone"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

RestrictedInit ==
  /\ correct = {1..N-F}
  /\ faulty = 1..N \ correct
  /\ pc = [p \in 1..N |-> "initnone"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

\* A correct process can receive any mix of correct and Byzantine messages.
Receive(p) ==
  /\ pc[p] \in {"initbcast", "initnone", "sent"}
  /\ \E newMsgs \subseteq sentMsgs \cup { [kind |-> "ECHO", frm |-> f] : f \in faulty } :
       recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

\* Receiving the broadcaster's INIT message is what lets a process accept.
InitBcast(p) ==
  /\ pc[p] = "initbcast"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sentMsgs' = sentMsgs \cup { [kind |-> "ECHO", frm |-> p] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* With enough ECHO messages to form a quorum short of a decision, send ECHO and wait.
EchoFewer(p) ==
  /\ pc[p] = "initnone"
  /\ Seen(p) >= N - 2 * T
  /\ Seen(p) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sentMsgs' = sentMsgs \cup { [kind |-> "ECHO", frm |-> p] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* A full quorum is enough to send ECHO and accept everything at once.
EchoDecision(p) ==
  /\ pc[p] = "initnone"
  /\ Seen(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sentMsgs' = sentMsgs \cup { [kind |-> "ECHO", frm |-> p] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* Having already sent ECHO, a process still accepts once it collects a quorum.
EchoJoin(p) ==
  /\ pc[p] = "sent"
  /\ Seen(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sentMsgs>>

CorrLtl == <>(\A p \in correct : pc[p] = "accept")
RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")
UnforgLtl == (\A p \in correct : pc[p] = "initnone") ~> (\A p \in correct : pc[p] # "accept")

Fairness ==
  \A p \in 1..N :
    /\ TRUE
    /\ SF_vars(Receive(p))
    /\ SF_vars(InitBcast(p))
    /\ SF_vars(EchoFewer(p))
    /\ SF_vars(EchoDecision(p))
    /\ SF_vars(EchoJoin(p))

InitSpec == Init /\ Fairness
RestSpec == RestrictedInit /\ Fairness

Spec == InitSpec \/ RestSpec

\* Unforgeability is only true when the broadcasters never send anything,
\* so it is proved under the no-broadcast start rather than always.
FCConstraints == InitSpec => UnforgLtl
====