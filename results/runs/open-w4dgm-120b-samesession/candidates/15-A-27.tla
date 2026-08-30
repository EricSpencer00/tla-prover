---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The protocol is one-round reliable broadcast (Srikanth & Toueg 1987);
\* the broadcaster is not modeled as a separate process: instead each
\* process starts either having received the broadcaster's INIT message
\* (the broadcast-received state) or not.  Correct processes obey the
\* protocol; Byzantine faulty processes may send arbitrary ECHO messages.

\* loc[p] is p's control location: Received means p got the INIT message
\* and immediately accepts and sends an ECHO.  SentEcho means p sent an
\* ECHO but has not yet accepted.  Accepted means p delivered the message.
\* recvMsgs[p] records the (sender, msgtype) pairs p has actually received.
\* sentMsgs is the set of messages sent by all correct processes so far.
\* correct and faulty partition the processes, with exactly F faults.

VARIABLES correct, faulty, loc, recvMsgs, sentMsgs

vars == <<correct, faulty, loc, recvMsgs, sentMsgs>>

Correct == {p \in 1..N : loc[p] \in {"Received", "SentEcho", "Accepted"}}
Faulty == {p \in 1..N : loc[p] = "Faulty"}
Echos(p) == {m.sender : m \in {x \in recvMsgs[p] : x.msgtype = "ECHO"}}
INIT0 == 1
NOINIT == 2

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ loc \in [1..N -> {"Received", "None", "SentEcho", "Accepted", "Faulty"}]
  /\ recvMsgs \in [1..N -> SUBSET [sender: 1..N, msgtype: {"ECHO"}]]
  /\ sentMsgs \subseteq [sender: 1..N, msgtype: {"ECHO"}]

Init ==
  /\ correct = {p \in 1..N : Cardinality({q \in 1..N : q <= p}) > N - F}
  /\ faulty = {1..N} \ correct
  /\ loc = [p \in 1..N |->
        IF p \in correct THEN
          IF p <= N - F THEN "Received" ELSE "None"
        ELSE "Faulty"]
  /\ recvMsgs = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

RestrInit ==
  /\ correct = {p \in 1..N : Cardinality({q \in 1..N : q <= p}) > N - F}
  /\ faulty = {1..N} \ correct
  /\ loc = [p \in 1..N |-> IF p \in correct THEN "None" ELSE "Faulty"]
  /\ recvMsgs = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

\* Correct processes may receive any fresh subset of the true sent set
\* plus arbitrary messages from Byzantine processes.
ReceiveSome(p) ==
  /\ loc[p] \in {"None", "SentEcho"}
  /\ \E S \in SUBSET (sentMsgs \cup
        {[sender |-> q, msgtype |-> "ECHO"] : q \in faulty}):
        recvMsgs' = [recvMsgs EXCEPT ![p] = S]
  /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

\* A correct process that received the broadcaster's INIT accepts immediately.
AcceptInit(p) ==
  /\ loc[p] = "Received"
  /\ loc' = [loc EXCEPT ![p] = "Accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> p, msgtype |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* If a correct process has not sent an ECHO but already has the
\* quorum of distinct senders, it sends one (it may be slow, it never fails).
SendEcho(p) ==
  /\ loc[p] = "None"
  /\ Cardinality(Echos(p)) >= N - 2 * T
  /\ loc' = [loc EXCEPT ![p] = "SentEcho"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> p, msgtype |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* A correct process with the full quorum both sends an ECHO and accepts.
AcceptEcho(p) ==
  /\ loc[p] = "None"
  /\ Cardinality(Echos(p)) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "Accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> p, msgtype |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* A correct process that has already sent an ECHO accepts once it has
\* the full quorum -- this is the slow-but-correct step.
CatchUpAccept(p) ==
  /\ loc[p] = "SentEcho"
  /\ Cardinality(Echos(p)) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

Next ==
  \/ \E p \in 1..N: ReceiveSome(p) \/ AcceptInit(p) \/ SendEcho(p)
                        \/ AcceptEcho(p) \/ CatchUpAccept(p)

Spec == Init /\ [][Next]_vars

CorrLtl == (Correct # {}) ~> (Correct \subseteq Correct)
RelayLtl == (\E p \in 1..N : loc[p] = "Accepted") ~> (Correct \subseteq Correct)

\* If no correct process broadcasts (all start in the non-broadcast state),
\* no correct process may ever accept -- a forged broadcast cannot appear.
UnforgLtl == (\A p \in 1..N : loc[p] # "Received") ~> (\A p \in 1..N : loc[p] # "Accepted")

FCConstraints ==
  /\ N \in Nat /\ N >= 1
  /\ T \in Nat /\ T >= 1
  /\ F \in Nat
  /\ N > 3 * T
  /\ T >= F
====