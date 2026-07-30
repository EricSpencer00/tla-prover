---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Location == {"init", "wait", "echoSent", "accept"}
MsgType == {"ECHO"}
Sender == 0..(N - 1)

VARIABLES correct, faulty, loc, recv, sentMsgs

vars == <<correct, faulty, loc, recv, sentMsgs>>

\* Message pairs: a sender id and a message kind; sentMsgs is what a Byzantine
\* sender may add to the pool at any time.
Message == [from : Sender, kind : MsgType]

TypeOK ==
    /\ correct \subseteq Sender
    /\ faulty \subseteq Sender
    /\ loc \in [Sender -> Location]
    /\ recv \in [Sender -> SUBSET Message]
    /\ sentMsgs \subseteq Message

\* A correct process may only ever act on messages it actually received.
FCConstraints ==
    /\ correct \cap faulty = {}
    /\ correct \cup faulty = Sender
    /\ Cardinality(correct) = N - F
    /\ \A p \in Sender : recv[p] \subseteq sentMsgs

Init ==
    /\ correct = {0, 1}
    /\ faulty = {2, 3}
    /\ loc = [p \in Sender |-> IF p \in {0, 1} THEN "init" ELSE "wait"]
    /\ recv = [p \in Sender |-> {}]
    /\ sentMsgs = {}

\* A second, larger configuration for the no-broadcast case.
InitLarge ==
    /\ correct = {0, 1, 2, 3, 4, 5, 6}
    /\ faulty = {7, 8, 9}
    /\ loc = [p \in Sender |-> IF p \in {0, 1, 2, 3, 4, 5, 6} THEN "wait" ELSE "wait"]
    /\ recv = [p \in Sender |-> {}]
    /\ sentMsgs = {}

\* A correct process receives some (possibly none) of the pool of messages: those
\* from correct senders, always present, plus any from Byzantine senders.
Receive(p) ==
    /\ loc[p] \in {"wait", "init"}
    /\ \E newMsgs \in SUBSET (sentMsgs \cup [from |-> Sender, kind |-> "ECHO"]) :
           recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

Broadcast(p, m) ==
    loc' = [loc EXCEPT ![p] = m]
    sentMsgs' = sentMsgs \cup {[from |-> p, kind |-> "ECHO"]}

EchoInit(p) ==
    /\ loc[p] = "init"
    /\ Broadcast(p, "echoSent")
    /\ loc' = [loc EXCEPT ![p] = "accept"]

EchoEarly(p) ==
    /\ loc[p] = "wait"
    /\ loc[p] # "echoSent"
    /\ Cardinality({msg \in recv[p] : msg.kind = "ECHO"}) >= N - 2 * T
    /\ Cardinality({msg \in recv[p] : msg.kind = "ECHO"}) < N - T
    /\ Broadcast(p, "echoSent")
    /\ UNCHANGED loc

EchoLate(p) ==
    /\ loc[p] = "wait"
    /\ loc[p] # "echoSent"
    /\ Cardinality({msg \in recv[p] : msg.kind = "ECHO"}) >= N - T
    /\ Broadcast(p, "accept")
    /\ UNCHANGED loc

AcceptEcho(p) ==
    /\ loc[p] = "echoSent"
    /\ Cardinality({msg \in recv[p] : msg.kind = "ECHO"}) >= N - T
    /\ Broadcast(p, "accept")
    /\ UNCHANGED loc

ReceiveStep == \E p \in Sender : Receive(p)
EchoInitStep == \E p \in Sender : EchoInit(p)
EchoEarlyStep == \E p \in Sender : EchoEarly(p)
EchoLateStep == \E p \in Sender : EchoLate(p)
AcceptEchoStep == \E p \in Sender : AcceptEcho(p)

Next ==
    \/ ReceiveStep
    \/ EchoInitStep
    \/ EchoEarlyStep
    \/ EchoLateStep
    \/ AcceptEchoStep

Spec ==
    /\ (Init \/ InitLarge)
    /\ [][Next]_vars
    /\ WF_vars(ReceiveStep)
    /\ WF_vars(EchoInitStep)
    /\ WF_vars(EchoEarlyStep)
    /\ WF_vars(EchoLateStep)
    /\ WF_vars(AcceptEchoStep)

\* Unforgeability: if no correct process ever broadcast, none ever accepts.
UnforgLtl ==
    (\A p \in Sender : p \in correct => loc[p] = "init")
        ~> (\A p \in Sender : p \in correct => loc[p] = "accept")

CorrLtl == ((\A p \in Sender : p \in correct => loc[p] = "init") ~>
            (\A p \in Sender : p \in correct => loc[p] = "accept"))

RelayLtl == (\E p \in Sender : p \in correct /\ loc[p] = "accept")
              ~> (\A p \in Sender : p \in correct => loc[p] = "accept")

====