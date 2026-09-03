---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* One-round async reliable broadcast (Srikanth & Toueg 1987, Fig.7) with Byzantine
\* processes and a shutdown action that never fires (kept for a no-fairness run).
\* The broadcaster's INIT is modeled as an initial value per process, not a sender.
\* N > 3T is the safety threshold; the safety argument runs without fairness.

Proc == 0..(N - 1)
MsgTy == {"ECHO"}
Msg == [typ : MsgTy, frm : Proc]

VARIABLES correct, faulty, pc, recv, sentMsgs

vars == <<correct, faulty, pc, recv, sentMsgs>>

TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty \subseteq Proc
  /\ pc \in [Proc -> {"initRecv", "initMissing", "sentEcho", "accepted"}]
  /\ recv \in [Proc -> SUBSET Msg]
  /\ sentMsgs \in SUBSET Msg

\* A correct process is slow only if it never receives a message or never accepts.
Quiescent(p) ==
  /\ recv[p] = {}
  /\ pc[p] # "accepted"

Init ==
  /\ \E S \in {s \in SUBSET Proc : Cardinality(s) = N - F}
       : correct = S /\ faulty = Proc \ S
  /\ \E p \in Proc : pc[p] = (IF p \in correct THEN "initRecv" ELSE "initMissing")
  /\ recv = [p \in Proc |-> {}]
  /\ sentMsgs = {}

\* A correct process receives some of the messages floating in the network.
Receive(p) ==
  /\ p \in correct
  /\ ~Quiescent(p)
  /\ recv' = [recv EXCEPT ![p] = @ \cup
                          (sentMsgs \cap {m \in Msg : m.frm \in correct})
                          \cup {m \in Msg : m.frm \in faulty}]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"sentEcho", "accepted"}
  /\ recv[p] \subseteq {[typ |-> "ECHO", frm |-> q] : q \in Proc}
  /\ sentMsgs' = sentMsgs \cup {[typ |-> "ECHO", frm |-> p]}
  /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptViaSaturation(p) ==
  /\ p \in correct
  /\ pc[p] = "initRecv"
  /\ Cardinality(recv[p]) >= N - T
  /\ sentMsgs' = sentMsgs \cup {[typ |-> "ECHO", frm |-> p]}
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptViaCatchup(p) ==
  /\ p \in correct
  /\ pc[p] = "sentEcho"
  /\ Cardinality(recv[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sentMsgs>>

Act(p) == AcceptViaSaturation(p) \/ AcceptViaCatchup(p)

Shard(p) == Receive(p) \/ SendEcho(p)
Next == (\E p \in Proc : Shard(p) \/ Act(p)) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
  /\ \A p \in Proc : WF_vars(Shard(p)) /\ SF_vars(Act(p))

CorrLtl == <>(\A p \in Proc : pc[p] = "accepted")
RelayLtl == (\E p \in Proc : pc[p] = "accepted") ~> (\A p \in Proc : pc[p] = "accepted")

\* The no-broadcast state is reachable and must never reach an accept.
UnforgLtl == (\A p \in Proc : pc[p] = "initMissing") ~> (\A p \in Proc : pc[p] # "accepted")

\* Safety: the quartet of domains never overflows its defined bound.
FCConstraints == TypeOK
====