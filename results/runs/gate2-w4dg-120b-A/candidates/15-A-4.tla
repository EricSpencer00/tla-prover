---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The action set is deliberately underspecified: correct processes may act on
\* whatever messages are currently in circulation, and Byzantine processes may
\* send arbitrary messages on top of that.
Corrects == 0..(N - F - 1)
Faulties == (N - F)..(N - 1)

Msgs == {"ECHO"}
MsgPairs == {<<s, m>> : s \in 0..(N - 1), m \in Msgs}

CtrlLoc == {"awaiting", "nobroadcast", "sentEcho", "accepted"}

VARIABLES corrects, faulties, loc, messages, sentpool

vars == <<corrects, faulties, loc, messages, sentpool>>

TypeOK ==
    /\ corrects \subseteq (0..(N - 1))
    /\ cardinality(corrects) = (N - F)
    /\ faulties = (0..(N - 1)) \ corrects
    /\ loc \in [0..(N - 1) -> CtrlLoc]
    /\ messages \in [0..(N - 1) -> SUBSET MsgPairs]
    /\ sentpool \subseteq MsgPairs

FCConstraints ==
    /\ N > (3 * T)
    /\ T >= F
    /\ F >= 0

Init ==
    /\ corrects = Corrects
    /\ loc = [p \in 0..(N - 1) |-> IF p \in Corrects THEN "awaiting" ELSE "nobroadcast"]
    /\ messages = [p \in 0..(N - 1) |-> {}]
    /\ sentpool = {}

InitNoBroadcast ==
    /\ corrects = Corrects
    /\ loc = [p \in 0..(N - 1) |-> "nobroadcast"]
    /\ messages = [p \in 0..(N - 1) |-> {}]
    /\ sentpool = {}

\* A correct process consumes whatever correct-send and Byzantine-send messages
\* happen to be in circulation; the receive set is nondeterministic.
Recv(p, newMsgs) ==
    /\ loc[p] \in {"awaiting", "nobroadcast"}
    /\ p \in corrects
    /\ newMsgs \subseteq (sentpool \cup MsgPairs)
    /\ messages' = [messages EXCEPT ![p] = messages[p] \cup newMsgs]
    /\ UNCHANGED <<corrects, faulties, loc, sentpool>>

\* A correct process that already received the INIT broadcast accepts and sends
\* an ECHO to everyone.
CatchInit(p) ==
    /\ loc[p] = "awaiting"
    /\ p \in corrects
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sentpool' = sentpool \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<corrects, faulties, messages>>

\* A correct process that has not sent ECHO yet receives a quorum just shy of
\* acceptance (N-2T to N-T inclusive) and sends ECHO but does not accept yet.
GatherEcho(p) ==
    /\ loc[p] = "awaiting"
    /\ p \in corrects
    /\ Cardinality({s \in 0..(N - 1) : <<s, "ECHO">> \in messages[p]}) >= (N - 2 * T)
    /\ Cardinality({s \in 0..(N - 1) : <<s, "ECHO">> \in messages[p]}) < (N - T)
    /\ loc' = [loc EXCEPT ![p] = "sentEcho"]
    /\ sentpool' = sentpool \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<corrects, faulties, messages>>

\* A correct process that has not sent ECHO yet receives a quorum large enough
\* to both send ECHO and accept immediately.
EchoAndAccept(p) ==
    /\ loc[p] = "awaiting"
    /\ p \in corrects
    /\ Cardinality({s \in 0..(N - 1) : <<s, "ECHO">> \in messages[p]}) >= (N - T)
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sentpool' = sentpool \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<corrects, faulties, messages>>

AcceptLater(p) ==
    /\ loc[p] = "sentEcho"
    /\ p \in corrects
    /\ Cardinality({s \in 0..(N - 1) : <<s, "ECHO">> \in messages[p]}) >= (N - T)
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<corrects, faulties, messages, sentpool>>

Next ==
    \/ \E p \in 0..(N - 1), newMsgs \in SUBSET (sentpool \cup MsgPairs) : Recv(p, newMsgs)
    \/ \E p \in 0..(N - 1) : CatchInit(p)
    \/ \E p \in 0..(N - 1) : GatherEcho(p)
    \/ \E p \in 0..(N - 1) : EchoAndAccept(p)
    \/ \E p \in 0..(N - 1) : AcceptLater(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 0..(N - 1), newMsgs \in SUBSET (sentpool \cup MsgPairs) : Recv(p, newMsgs))
    /\ WF_vars(\E p \in 0..(N - 1) : EchoAndAccept(p) \/ AcceptLater(p))

CorrLtl == (\A p \in corrects : loc[p] = "awaiting") ~> (\A p \in corrects : loc[p] = "accepted")

RelayLtl == (\E p \in corrects : loc[p] = "accepted") ~> (\A p \in corrects : loc[p] = "accepted")

\* Safety: if no correct process broadcast, none accepts.
UnforgLtl == (\A p \in corrects : loc[p] = "nobroadcast") ~> (\A p \in corrects : loc[p] # "accepted")

====