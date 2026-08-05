---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A reliable broadcast protocol tolerating up to T Byzantine processes. The
\* broadcaster is modeled as an initial configuration: a process either
\* "received" the broadcaster's INIT message (set to broadcast state) or
\* did not (set to non-broadcast state) at the start. Correct processes
\* send ECHO messages and accept once they collect enough distinct ECHOs.
\* The broadcast state is never entered by a BMP; only the one broadcast
\* process (identified by its initial state) ever sends it.

Procs == 1..N
Echoes == [pid : Procs, kind : {"ECHO"}]
NoProc == 0
PcSpace == {"nocast", "ibcast", "sent", "accp"}

VARIABLES corrects, faulty, pc, rcvd, sentMsgs

vars == << corrects, faulty, pc, rcvd, sentMsgs >>

TypeOK ==
  /\ corrects \subseteq Procs
  /\ faulty \subseteq Procs
  /\ pc \in [Procs -> PcSpace]
  /\ rcvd \in [Procs -> SUBSET Echoes]
  /\ sentMsgs \subseteq Echoes

Init ==
  /\ corrects = {1..(N-F)}
  /\ faulty = Procs \ {1..(N-F)}
  /\ pc = [p \in Procs |-> IF p <= (N-F) THEN ibcast ELSE nocast]
  /\ rcvd = [p \in Procs |-> {}]
  /\ sentMsgs = {}

\* A correct process receives some new messages (in bulk, nondeterministically).
\* Faulty processes may send arbitrary ECHOs; correct-sent ones are in sentMsgs.
Receive(p) ==
  /\ pc[p] \in {"nocast", "ibcast"}
  /\ \E new \subseteq (sentMsgs \cup [pid |-> NoProc, kind |-> "ECHO"]):
       rcvd' = [rcvd EXCEPT ![p] = @ \cup new]
  /\ UNCHANGED << corrects, faulty, pc, sentMsgs >>

\* The broadcast process, which already holds the INIT message, accepts and
\* sends an ECHO to all immediately (no quorum needed, it is the source).
BroadcastSelf(p) ==
  /\ p \in corrects
  /\ pc[p] = ibcast
  /\ pc' = [pc EXCEPT ![p] = "accp"]
  /\ sentMsgs' = sentMsgs \cup {[pid |-> p, kind |-> "ECHO"]}
  /\ UNCHANGED << corrects, faulty, rcvd >>

\* Slow case: a correct process gathers a "large enough" set of ECHOs to
\* send its own ECHO but cannot yet accept (not enough distinct senders).
RelayEcho(p) ==
  /\ p \in corrects
  /\ pc[p] \in {"nocast", "ibcast"}
  /\ Cardinality({m \in rcvd[p] : m.kind = "ECHO"}) >= (N - 2*T)
  /\ Cardinality({m \in rcvd[p] : m.kind = "ECHO"}) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {[pid |-> p, kind |-> "ECHO"]}
  /\ UNCHANGED << corrects, faulty, rcvd >>

\* Fast case: a correct process gathers a quorum of ECHOs and accepts
\* without waiting to relay its own ECHO.
BecomeAcceptor(p) ==
  /\ p \in corrects
  /\ pc[p] \in {"nocast", "ibcast"}
  /\ Cardinality({m \in rcvd[p] : m.kind = "ECHO"}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accp"]
  /\ sentMsgs' = sentMsgs \cup {[pid |-> p, kind |-> "ECHO"]}
  /\ UNCHANGED << corrects, faulty, rcvd >>

RelayAccept(p) ==
  /\ p \in corrects
  /\ pc[p] = "sent"
  /\ Cardinality({m \in rcvd[p] : m.kind = "ECHO"}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accp"]
  /\ UNCHANGED << corrects, faulty, rcvd, sentMsgs >>

Next ==
  \E p \in Procs:
    \/ Receive(p)
    \/ BroadcastSelf(p)
    \/ RelayEcho(p)
    \/ BecomeAcceptor(p)
    \/ RelayAccept(p)

\* Weak fairness on each correct process's combined receive-and-act steps
\* (receive, broadcast-self, relay-echo, become-acceptor, relay-accept)
\* ensures a slow-but-correct process eventually makes progress.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in corrects:
       (WF_vars(Receive(p) \/ BroadcastSelf(p) \/ RelayEcho(p) \/ BecomeAcceptor(p) \/ RelayAccept(p)))

\* The broadcast state is never entered by a BMP. The only live process that
\* can do it is the one that already received the broadcaster's INIT message.
CorrLtl == (pc[1] = ibcast) ~> (\A p \in corrects : pc[p] = "accp")

RelayLtl == (\E p \in corrects : pc[p] = "accp") ~> (\A p \in corrects : pc[p] = "accp")

\* If nobody broadcast at all (no process started in the broadcast state),
\* then nobody accepting is an artifact of the protocol, not a trace bug.
UnforgLtl == (pc[1] = nocast) ~> (\A p \in corrects : pc[p] # "accp")

CorrLtlFA == (pc[1] = ibcast) ~> (\A p \in corrects : pc[p] = "accp")
RelayLtlFA == (\E p \in corrects : pc[p] = "accp") ~> (\A p \in corrects : pc[p] = "accp")

\* The broadcast state is a runtime fact about identity (0 is not a process),
\* so it never changes once set.
FCConstraints ==
  \A p \in Procs: pc[p] = ibcast => p # NoProc

====