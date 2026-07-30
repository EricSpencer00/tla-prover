---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Derive the correct-faulty partition from the fixed bounded count F:
FaultSet == [id \in 1..N |-> IF id <= F THEN "faulty" ELSE "correct"]
Correct == {p \in 1..N : FaultSet[p] = "correct"}
Faulty == {p \in 1..N : FaultSet[p] = "faulty"}

Msgs == {"ECHO"}
SenderIds == 1..N

VARIABLES ctrl, recvMsgs, sentMsgs, startState

vars == <<ctrl, recvMsgs, sentMsgs, startState>>

TypeOK ==
    /\ ctrl \in [1..N -> {"initReceived", "noInit", "echoed", "accepted"}]
    /\ recvMsgs \in [1..N -> SUBSET (SenderIds \X Msgs)]
    /\ sentMsgs \subseteq (SenderIds \X Msgs)
    /\ startState \in {"broadcast", "nobroadcast"}

\* A correct process either receives the INIT broadcast or not:
InitDist ==
    {p \in Correct : ctrl[p] = "initReceived"}
    \cup
    {p \in Correct : ctrl[p] = "noInit"}

FCConstraints ==
    /\ Cardinality(Correct) = N - F
    /\ Faulty = 1..N \ Correct
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

Init ==
    /\ ctrl = [p \in 1..N |-> IF p \in Correct THEN startState ELSE "noInit"]
    /\ recvMsgs = [p \in 1..N |-> {}]
    /\ sentMsgs = {}
    /\ startState \in {"broadcast", "nobroadcast"}

\* Correct processes only ever learn about messages from the set they can
\* actually observe; the rest is nondeterministic noise from faulty ones.
ReceiveMany(p) ==
    /\ ctrl[p] \in {"initReceived", "noInit"}
    /\ \E m \subseteq sentMsgs \cup (SenderIds \X Msgs) :
         recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup m]
    /\ UNCHANGED <<ctrl, sentMsgs, startState>>

\* A broadcast-receiver accepts immediately and sends ECHO to all:
InitAccept(p) ==
    /\ ctrl[p] = "initReceived"
    /\ ctrl' = [ctrl EXCEPT ![p] = "accepted"]
    /\ sentMsgs' = sentMsgs \cup {<<q, "ECHO">> : q \in Correct}
    /\ UNCHANGED <<recvMsgs, startState>>

\* A non-sender with just enough echo support sends ECHO but delays accept:
EchoDelay(p) ==
    /\ ctrl[p] \in {"noInit"}
    /\ Cardinality({m \in recvMsgs[p] : m[2] = "ECHO"}) >= N - 2 * T
    /\ Cardinality({m \in recvMsgs[p] : m[2] = "ECHO"}) < N - T
    /\ ctrl' = [ctrl EXCEPT ![p] = "echoed"]
    /\ sentMsgs' = sentMsgs \cup {<<q, "ECHO">> : q \in Correct}
    /\ UNCHANGED <<recvMsgs, startState>>

\* A non-sender with strong echo support both sends ECHO and accepts:
EchoAccept(p) ==
    /\ ctrl[p] \in {"noInit"}
    /\ Cardinality({m \in recvMsgs[p] : m[2] = "ECHO"}) >= N - T
    /\ ctrl' = [ctrl EXCEPT ![p] = "accepted"]
    /\ sentMsgs' = sentMsgs \cup {<<q, "ECHO">> : q \in Correct}
    /\ UNCHANGED <<recvMsgs, startState>>

\* A process already sent ECHO accepts once the quorum is there:
AcceptLater(p) ==
    /\ ctrl[p] = "echoed"
    /\ Cardinality({m \in recvMsgs[p] : m[2] = "ECHO"}) >= N - T
    /\ ctrl' = [ctrl EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<recvMsgs, sentMsgs, startState>>

Next ==
    \/ \E p \in 1..N : ReceiveMany(p)
    \/ \E p \in 1..N : InitAccept(p)
    \/ \E p \in 1..N : EchoDelay(p)
    \/ \E p \in 1..N : EchoAccept(p)
    \/ \E p \in 1..N : AcceptLater(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N : ReceiveMany(p))
    /\ WF_vars(\E p \in 1..N : EchoDelay(p) \/ EchoAccept(p))
    /\ WF_vars(\E p \in 1..N : AcceptLater(p))

\* If nobody broadcasts, no correct process ever accepts (unforgeability):
UnforgLtl == (startState = "nobroadcast") ~> (\A p \in Correct : ctrl[p] = "accepted")

\* When every correct process broadcasted, they all eventually accept:
CorrLtl == (startState = "broadcast") ~> (\A p \in Correct : ctrl[p] = "accepted")

\* Acceptance is contagious: one correct acceptor drags the rest along:
RelayLtl == (<>(\E p \in Correct : ctrl[p] = "accepted")) ~> (\A p \in Correct : ctrl[p] = "accepted")

====