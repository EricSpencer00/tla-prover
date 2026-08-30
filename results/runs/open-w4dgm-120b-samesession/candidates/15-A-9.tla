---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

(* Model of a one-round asynchronous reliable broadcast with Byzantine faults,  *)
(* based on Srikanth and Toueg 1987, Figure 7.  A broadcaster sends INIT to   *)
(* correct processes and they echo; a correct process accepts once it has    *)
(* received sufficiently many distinct ECHO messages.  Byzantine processes   *)
(* may send arbitrary ECHO messages.  Safety: no acceptance without any       *)
(* broadcast.  Liveness: acceptance by all correct processes.               *)

CONSTANTS N, T, F

\* Control locations: a process may start with the broadcaster's INIT already  *
(* received (receivedBroadcast) or not (noBroadcast).  The two initial      *)
(* states model whether the broadcaster succeeded in reaching that process. *)
Locations == {"noBroadcast", "receivedBroadcast", "sentEcho", "accepted"}

VARIABLES correct, faulty, loc, recvMsgs, sentMsgs

vars == <<correct, faulty, loc, recvMsgs, sentMsgs>>

\* A received message is a pair of the sender's identity and an ECHO tag.
Message == [sender : 1..N, kind : {"ECHO"}]

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Locations]
  /\ recvMsgs \in [1..N -> SUBSET Message]
  /\ sentMsgs \subseteq Message

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ {1..(N - F)}
  /\ loc \in [n \in 1..N |-> CHOOSE l \in Locations : l \in {"receivedBroadcast", "noBroadcast"}]
  /\ recvMsgs = [n \in 1..N |-> {}]
  /\ sentMsgs = {}

\* A correct process receives any subset of what correct senders broadcast and
\* any single message from a faulty sender; it may also simply receive nothing.
Receive(n) ==
  /\ loc[n] \in {"receivedBroadcast", "sentEcho"}
  /\ \E m \in SUBSET {msg \in sentMsgs : msg.sender \in correct} \cup
                     {msg \in [Message -> msg.kind \in {"ECHO"}] : msg.sender \in faulty} :
       recvMsgs' = [recvMsgs EXCEPT ![n] = @ \cup m]
  /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

SendEcho(n) ==
  /\ loc[n] = "receivedBroadcast"
  /\ loc' = [loc EXCEPT ![n] = "sentEcho"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> n, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* Less than N-T distinct ECHOs gathered: broadcast but do not accept yet.
Broadcast(n) ==
  /\ loc[n] = "noBroadcast"
  /\ Cardinality({msg \in recvMsgs[n] : msg.kind = "ECHO"}) >= (N - 2 * T)
  /\ Cardinality({msg \in recvMsgs[n] : msg.kind = "ECHO"}) < (N - T)
  /\ loc' = [loc EXCEPT ![n] = "sentEcho"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> n, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* Enough distinct ECHOs gathered: broadcast and accept in the same step.
AcceptAndBroadcast(n) ==
  /\ loc[n] \in {"noBroadcast", "sentEcho"}
  /\ loc[n] # "accepted"
  /\ Cardinality({msg \in recvMsgs[n] : msg.kind = "ECHO"}) >= (N - T)
  /\ loc' = [loc EXCEPT ![n] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> n, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

AcceptQuietly(n) ==
  /\ loc[n] = "sentEcho"
  /\ loc[n] # "accepted"
  /\ Cardinality({msg \in recvMsgs[n] : msg.kind = "ECHO"}) >= (N - T)
  /\ loc' = [loc EXCEPT ![n] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

\* Receiving new messages is weakly fair for each correct process, so a process
\* that can forever keep receiving from correct senders eventually does.
Next ==
  \/ \E n \in correct : Receive(n) \/ SendEcho(n) \/ Broadcast(n)
                          \/ AcceptAndBroadcast(n) \/ AcceptQuietly(n)
  \/ \E n \in faulty : \E m \in SUBSET Message : recvMsgs' = [recvMsgs EXCEPT ![n] = @ \cup m]
  \/ UNCHANGED <<correct, faulty, loc, sentMsgs>>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in correct : SendEcho(n))
  /\ \A n \in correct : WF_vars(Receive(n))

CorrLtl == (\A n \in correct : loc[n] = "receivedBroadcast") ~> (\A n \in correct : loc[n] = "accepted")
RelayLtl == (\E n \in correct : loc[n] = "accepted") ~> (\A n \in correct : loc[n] = "accepted")

\* No correct process has broadcast and accepted unless some correct process
\* actually received the broadcaster's INIT message.
FCConstraints == (\A n \in correct : loc[n] = "accepted") => (\E n \in correct : loc[n] = "receivedBroadcast")

\* Safety only: no broadcast implies no acceptance, without liveness.
UnforgLtl == (\A n \in correct : loc[n] # "receivedBroadcast") ~> (\A n \in correct : loc[n] # "accepted")

====