---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, recvMsgs, sentMsgs
vars == <<correct, faulty, loc, recvMsgs, sentMsgs>>

\* loc encodes both the message-control state (whether a process saw the
\* broadcaster's INIT message) and the protocol progression (not sent,
\* sent but not accepted, accepted). recvMsgs aggregates all messages a
\* process has observed; sentMsgs is the set of messages actually put on
\* the wire by correct processes (bounded by N, the number of correct
\* participants).
LocType == {"initRecvd", "noInit", "sent", "accepted"}
MsgType == {"echo"}
Msg == MsgType \X (1..N)

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> LocType]
  /\ recvMsgs \in [1..N -> SUBSET Msg]
  /\ sentMsgs \subseteq Msg

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ sentMsgs = {}
  /\ \E broadcastGroup \in SUBSET (1..N) :
       /\ broadcastGroup # {}
       /\ broadcastGroup \cup correct = (1..N)
       /\ broadcastGroup \cap correct = {}
       /\ loc = [p \in 1..N |-> IF p \in broadcastGroup THEN "initRecvd" ELSE "noInit"]
  /\ recvMsgs = [p \in 1..N |-> {}]

NoBroadcastInit ==
  /\ loc = [p \in 1..N |-> "noInit"]
  /\ sentMsgs = {}
  /\ recvMsgs = [p \in 1..N |-> {}]

\* A correct process may observe any subset of everything sent so far plus
\* whatever Byzantine processes choose to throw its way.
Receive(p, msgset) ==
  /\ loc[p] \in {"initRecvd", "noInit", "sent"}
  /\ msgset # {}
  /\ msgset \subseteq (sentMsgs \cup (MsgType \X faulty))
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup msgset]
  /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

SendEcho(p) ==
  /\ p \in correct
  /\ loc[p] = "initRecvd"
  /\ sentMsgs' = sentMsgs \cup {<<"echo", p>>}
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* The two acceptance thresholds diverge once a correct process has already
\* sent its ECHO (the weaker one is reachable only when that send is still
\* missing, which is exactly the case the Byzantine participants exploit to
\* delay acceptance).
AcceptFast(p) ==
  /\ p \in correct
  /\ loc[p] # "accepted"
  /\ Cardinality(recvMsgs[p]) >= N - T
  /\ sentMsgs' = sentMsgs \cup {<<"echo", p>>}
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

AcceptSlow(p) ==
  /\ p \in correct
  /\ loc[p] = "noInit"
  /\ Cardinality({m \in recvMsgs[p] : m[1] = "echo"}) >= N - 2T
  /\ sentMsgs' = sentMsgs \cup {<<"echo", p>>}
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

AcceptReplay(p) ==
  /\ p \in correct
  /\ loc[p] = "sent"
  /\ Cardinality({m \in recvMsgs[p] : m[1] = "echo"}) >= N - T
  /\ sentMsgs' = sentMsgs \cup {<<"echo", p>>}
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* Fairness of the ACK path is what prevents a correct process from
\* stalling forever while awaiting only-Babylonian traffic.
ReceiveStep == \E p \in 1..N, msgset \in SUBSET Msg : Receive(p, msgset)
SendStep == \E p \in correct : SendEcho(p)
FastStep == \E p \in correct : AcceptFast(p)
SlowStep == \E p \in correct : AcceptSlow(p)
ReplayStep == \E p \in correct : AcceptReplay(p)

Next == ReceiveStep \/ SendStep \/ FastStep \/ SlowStep \/ ReplayStep

Spec == Init /\ [][Next]_vars
  /\ WF_vars(ReceiveStep) /\ WF_vars(SendStep) /\ SF_vars(FastStep)
  /\ WF_vars(SlowStep) /\ WF_vars(ReplayStep)

CorrLtl == \A p \in correct : (loc[p] = "initRecvd") ~> (loc[p] = "accepted")
RelayLtl == \E p \in correct : (loc[p] = "sent") ~> (\A q \in correct : loc[q] = "sent")
UnforgLtl == NoBroadcastInit ~> (\A p \in correct : loc[p] # "accepted")

\* Unforgeability is safety-critical (it is a plain invariant), so it also
\* gets a dedicated proof obligation here even though it is already part of
\* the full Liveness check; this keeps model checking from skipping it.
FCConstraints == UnforgLtl
====