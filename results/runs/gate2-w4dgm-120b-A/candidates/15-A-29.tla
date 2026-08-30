---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process may be in one of three control locations: idle, waiting after
\* broadcasting ECHO, or accepted (delivered). msgLog[p] is the set of
\* (sender, kind)-messages p has received so far.
VARIABLES correct, faulty, loc, msgLog, sentMsgs

vars == <<correct, faulty, loc, msgLog, sentMsgs>>

InitLoc == "init"
EchoLoc == "echo"
AcceptLoc == "accept"
NoneMsg == [sender |-> 0, kind |-> "none"]
EchoMsg(s) == [sender |-> s, kind |-> "ECHO"]
InitMsg(s) == [sender |-> s, kind |-> "INIT"]
AllEchoes == {EchoMsg(s) : s \in 1..N}

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ loc \in [1..N -> {"idle", "echo", "accept"}]
    /\ msgLog \in [1..N -> SUBSET AllEchoes]
    /\ sentMsgs \subseteq AllEchoes

\* Broadcast-unforgeability: if no correct process ever broadcast INIT,
\* then no correct process ever accepts.
FCConstraints ==
    /\ correct \cup faulty = (1..N)
    /\ (correct \cap faulty = {})
    /\ (N > 3 * T)
    /\ (T >= F)
    /\ (F >= 0)

Init ==
    /\ correct = {1..(N - F)}
    /\ faulty = {(N - F + 1)..N}
    /\ loc = [p \in 1..N |-> IF p <= (N - F) THEN InitLoc ELSE "idle"]
    /\ msgLog = [p \in 1..N |-> {}]
    /\ sentMsgs = {}

\* A correct process may pick up any subset of the universe of messages it
\* has not seen yet, so a correct process can be slow on delivery.
ReceiveMsgs(p) ==
    /\ loc[p] \in {"idle", "echo"}
    /\ \E S \in SUBSET AllEchoes :
        LET unseen == S \ msgLog[p] IN
        /\ unseen # {}
        /\ msgLog' = [msgLog EXCEPT ![p] = @ \cup unseen]
    /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

\* A correct process that received the broadcaster's INIT message accepts
\* immediately and broadcasts an ECHO to everyone.
BroadcastEcho(p) ==
    /\ loc[p] = InitLoc
    /\ loc' = [loc EXCEPT ![p] = AcceptLoc]
    /\ sentMsgs' = sentMsgs \cup {EchoMsg(p)}
    /\ UNCHANGED <<correct, faulty, msgLog>>

\* If a correct process has not broadcast yet but has received at least
\* N-2T (resp. N-T) distinct ECHO messages from senders, it broadcasts
\* one itself, and accepts only if it already had at least N-T.
RelayEcho(p) ==
    /\ loc[p] = "idle"
    /\ Cardinality(msgLog[p]) >= (N - 2 * T)
    /\ sentMsgs' = sentMsgs \cup {EchoMsg(p)}
    /\ loc' = IF Cardinality(msgLog[p]) >= (N - T) THEN AcceptLoc ELSE EchoLoc
    /\ UNCHANGED <<correct, faulty, msgLog>>

AcceptRelay(p) ==
    /\ loc[p] = EchoLoc
    /\ Cardinality(msgLog[p]) >= (N - T)
    /\ loc' = [loc EXCEPT ![p] = AcceptLoc]
    /\ UNCHANGED <<correct, faulty, msgLog, sentMsgs>>

Next ==
    \/ \E p \in 1..N : ReceiveMsgs(p)
    \/ \E p \in correct : BroadcastEcho(p)
    \/ \E p \in correct : RelayEcho(p)
    \/ \E p \in correct : AcceptRelay(p)

Spec == Init /\ [][Next]_vars
    /\ \A p \in correct : WF_vars(ReceiveMsgs(p))
    /\ \A p \in correct : WF_vars(RelayEcho(p))
    /\ \A p \in correct : WF_vars(AcceptRelay(p))

\* If every correct process received the broadcaster's INIT message, then
\* all correct processes eventually accept.
CorrLtl ==
    /\ \A p \in correct : loc[p] = InitLoc
    /\ \A p \in correct : (loc[p] # InitLoc) ~> (loc[p] = AcceptLoc)

\* Every acceptance by a correct process eventually spreads to all correct
\* processes.
RelayLtl ==
    /\ \E p \in correct : (loc[p] = AcceptLoc)
    /\ (\E p \in correct : loc[p] = AcceptLoc) ~> (\A q \in correct : loc[q] = AcceptLoc)

\* If no correct process broadcasts INIT, no correct process accepts.
UnforgLtl ==
    (\A p \in correct : loc[p] # InitLoc) ~> (\A p \in correct : loc[p] # AcceptLoc)

====