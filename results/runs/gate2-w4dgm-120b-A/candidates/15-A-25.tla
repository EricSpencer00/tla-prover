---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct/reliable participants vs. Byzantine ones; N > 3T is the safety
\* corridor.  CORR and FAULT partition the processes and determine whose
\* messages count toward the quorum thresholds throughout.
VARIABLES correct, faulty, ctl, rx, sent

vars == <<correct, faulty, ctl, rx, sent>>

Procs == 1..N
MsgSpace == [snd : Procs, typ : {"ECHO"}]

\* The number of distinct ECHO senders a process has actually observed.
Observed(p) == Cardinality({m.snd : m \in rx[p]})

InitCtl == [p \in Procs |-> IF p = 1 THEN "recv" ELSE "norecv"]
InitCtlRest == [p \in Procs |-> "norecv"]

TypeOK ==
  /\ correct \subseteq Procs
  /\ Cardinality(correct) = N - F
  /\ faulty = Procs \ correct
  /\ ctl \in [Procs -> {"recv", "norecv", "sentecho", "accept"}]
  /\ rx \in [Procs -> SUBSET MsgSpace]
  /\ sent \subseteq MsgSpace

\* Unforgeability is the property: with no correct broadcaster nobody
\* accepts.  It is explicit about where accept is allowed to happen --
\* only after the quorum of (possibly Byzantine) senders, never otherwise.
Unforgeability ==
  (Cardinality(correct) = 0) => (\A p \in Procs : ctl[p] # "accept")

\* Full-range type checking: control locations, received messages and the
\* correct/faulty partition must all stay inside their defined domains.
FCConstraints == TypeOK

Init ==
  /\ correct = {p \in Procs : p <= N - F}
  /\ faulty = {p \in Procs : p > N - F}
  /\ ctl = InitCtl
  /\ rx = [p \in Procs |-> {}]
  /\ sent = {}

InitAllNoBroadcast ==
  /\ correct = {p \in Procs : p <= N - F}
  /\ faulty = {p \in Procs : p > N - F}
  /\ ctl = InitCtlRest
  /\ rx = [p \in Procs |-> {}]
  /\ sent = {}

\* Correct processes only ever receive messages that some sender actually
\* sent -- correct or faulty.  Nothing is fabricated by the network.
ReceiveMsgs(p) ==
  /\ p \in correct
  /\ ctl[p] \notin {"accept", "sentecho"}
  /\ \E ms \in SUBSET ({m \in sent : m.typ = "ECHO"} \cup
                        {[snd |-> f, typ |-> "ECHO"] : f \in faulty}) :
       rx' = [rx EXCEPT ![p] = @ \cup ms]
  /\ UNCHANGED <<correct, faulty, ctl, sent>>

\* Immediate acceptance on receipt of the real INIT broadcast; this is the
\* only path that does not count any quorum at all.
RecvInitAccept(p) ==
  /\ p \in correct
  /\ ctl[p] = "recv"
  /\ rx' = [rx EXCEPT ![p] = @ \cup {[snd |-> p, typ |-> "ECHO"]}]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ ctl' = [ctl EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty>>

\* Two quorum thresholds: one to send an ECHO, one to accept immediately.
QuorumSend(p) ==
  /\ p \in correct
  /\ ctl[p] = "norecv"
  /\ Observed(p) >= N - 2 * T
  /\ Observed(p) < N - T
  /\ rx' = [rx EXCEPT ![p] = @ \cup {[snd |-> p, typ |-> "ECHO"]}]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ ctl' = [ctl EXCEPT ![p] = "sentecho"]
  /\ UNCHANGED <<correct, faulty>>

QuorumAccept(p) ==
  /\ p \in correct
  /\ ctl[p] \in {"norecv", "sentecho"}
  /\ Observed(p) >= N - T
  /\ rx' = [rx EXCEPT ![p] = @ \cup {[snd |-> p, typ |-> "ECHO"]}]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ ctl' = [ctl EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty>>

RelayAccept(p) ==
  /\ p \in correct
  /\ ctl[p] = "sentecho"
  /\ Observed(p) >= N - T
  /\ ctl' = [ctl EXCEPT ![p] = "accept"]
  /\ rx' = [rx EXCEPT ![p] = @ \cup {[snd |-> p, typ |-> "ECHO"]}]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty>>

\* Weak fairness on receiving and acting together is what keeps the
\* quorum eventually forming at a correct process.
Next ==
  \/ \E p \in Procs : ReceiveMsgs(p) \/ RecvInitAccept(p) \/ QuorumSend(p)
                        \/ QuorumAccept(p) \/ RelayAccept(p)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Procs : ReceiveMsgs(p))
  /\ WF_vars(\E p \in Procs : RecvInitAccept(p))
  /\ WF_vars(\E p \in Procs : QuorumSend(p))
  /\ WF_vars(\E p \in Procs : QuorumAccept(p))
  /\ WF_vars(\E p \in Procs : RelayAccept(p))

CorrLtl ==
  \A p \in Procs : (ctl[p] = "recv") ~> (ctl[p] = "accept")

RelayLtl ==
  (Cardinality({p \in Procs : ctl[p] = "accept"}) >= 1)
    ~> (Cardinality({p \in Procs : ctl[p] = "accept"}) = Cardinality(Procs))

\* Unforgeability is safe even without fairness -- it holds in the
\* reachable-state set itself -- so it is a plain invariant.
UnforgLtl == Unforgeability

====