---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Control locations of the one-round broadcast protocol
Locations == {"init", "noinit", "sent", "accept"}

VARIABLES corrects, faultys, loc, inbox, sentMsgs

vars == <<corrects, faultys, loc, inbox, sentMsgs>>

InitLocs == {"init", "noinit"}

Messages == {"echo"}

TypeOK ==
    /\ corrects \subseteq (1..N)
    /\ Cardinality(corrects) = N - F
    /\ faultys = (1..N) \ corrects
    /\ loc \in [1..N -> Locations]
    /\ inbox \in [1..N -> SUBSET (1..N \X Messages)]
    /\ sentMsgs \subseteq (1..N \X Messages)

Init ==
    /\ corrects = {1, 2, 3}
    /\ faultys = {4}
    /\ loc = [p \in 1..N |-> IF p <= 3 THEN "init" ELSE "noinit"]
    /\ inbox = [p \in 1..N |-> {}]
    /\ sentMsgs = {}

\* No-broadcast initial state: nobody receives the INIT message
InitNoBroadcast ==
    /\ corrects = {1, 2, 3}
    /\ faultys = {4}
    /\ loc = [p \in 1..N |-> "noinit"]
    /\ inbox = [p \in 1..N |-> {}]
    /\ sentMsgs = {}

\* Any message a correct process could receive: a correct-sent one, or a
\* Byzantine one (the former is always available once it has been sent)
AnyMsgs(p) ==
    (sentMsgs \cup (faultys \X Messages))

\* A correct process receives a set of new messages, only from the above set
ReceiveMsg(p) ==
    /\ p \in corrects
    /\ loc[p] \notin {"sent", "accept"}
    /\ \E new \in SUBSET AnyMsgs(p) :
         inbox' = [inbox EXCEPT ![p] = inbox[p] \cup new]
    /\ UNCHANGED <<corrects, faultys, loc, sentMsgs>>

\* A correct participant that received the INIT broadcast accepts immediately
SendAndAccept(p) ==
    /\ p \in corrects
    /\ loc[p] = "init"
    /\ loc' = [loc EXCEPT ![p] = "accept"]
    /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
    /\ UNCHANGED <<corrects, faultys, inbox>>

\* A correct participant that has not yet sent ECHO gathers enough spurious
\* ECHO messages to send, but not enough to accept yet
SendEchoOnly(p) ==
    /\ p \in corrects
    /\ loc[p] = "noinit"
    /\ Cardinality({q \in inbox[p] : q[2] = "echo"}) >= N - 2 * T
    /\ Cardinality({q \in inbox[p] : q[2] = "echo"}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "sent"]
    /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
    /\ UNCHANGED <<corrects, faultys, inbox>>

\* A correct participant that has not yet sent ECHO gathers enough to send
\* and accept in the same step
SendEchoAndAccept(p) ==
    /\ p \in corrects
    /\ loc[p] = "noinit"
    /\ Cardinality({q \in inbox[p] : q[2] = "echo"}) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accept"]
    /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
    /\ UNCHANGED <<corrects, faultys, inbox>>

\* A correct participant that has already sent ECHO accepts
Accept(p) ==
    /\ p \in corrects
    /\ loc[p] = "sent"
    /\ Cardinality({q \in inbox[p] : q[2] = "echo"}) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<corrects, faultys, inbox, sentMsgs>>

\* A correct participant may always receive and act again, so this needs
\* fairness to keep it from being stalled forever by the environment
Next ==
    \/ \E p \in 1..N : ReceiveMsg(p) \/ SendAndAccept(p) \/ SendEchoOnly(p)
                         \/ SendEchoAndAccept(p) \/ Accept(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N : ReceiveMsg(p))
    /\ WF_vars(\E p \in 1..N : SendAndAccept(p))
    /\ WF_vars(\E p \in 1..N : SendEchoOnly(p))
    /\ WF_vars(\E p \in 1..N : SendEchoAndAccept(p))
    /\ WF_vars(\E p \in 1..N : Accept(p))

\* The no-broadcast run needs a version of the spec without fairness to
\* check unforgeability as a plain reachability property
SpecNoFair ==
    /\ InitNoBroadcast
    /\ [][Next]_vars

AllAccepted == \A p \in corrects : loc[p] = "accept"

CorrLtl == (N - F = 3) ~> AllAccepted
RelayLtl == (LocExists("accept") /\ ~AllAccepted) ~> AllAccepted
UnforgLtl == LocExists("accept") ~> (LocExists("init") /\ ~AllAccepted)

LocExists(l) == \E p \in 1..N : loc[p] = l

FCConstraints == UnforgLtl

====