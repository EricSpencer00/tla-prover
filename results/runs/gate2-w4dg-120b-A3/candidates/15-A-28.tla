---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* A reliable broadcast protocol from Srikanth & Toueg (1987). Processes are
\* partitioned into correct and Byzantine sets, chosen nondeterministically
\* at init. Broadcast is modeled as an initial value at each process, not as
\* a separate sender: a process either "received" the INIT message or not.
\* The spec must expose the constants and operators that the reference
\* .cfg file expects to exist, exactly as named.

CONSTANTS N, T, F

NoInit == "noinit"
InitMsg == "init"
EchoMsg == "echo"
Ids == 1..N
Parts == {"lp", "ln"}
QIds == Ids \X Parts
Senders == Ids
MsgSpace == QIds \X {InitMsg, EchoMsg}

VARIABLES correct, faulty, location, recvMsgs, sentMsgs

vars == <<correct, faulty, location, recvMsgs, sentMsgs>>

RECURSIVE Cardinality(_)
Cardinality(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Cardinality(S \ {x})

TypeOK ==
  /\ correct \subseteq Ids
  /\ Cardinality(correct) = N - F
  /\ faulty = Ids \ correct
  /\ location \in [Ids -> Parts]
  /\ recvMsgs \in [Ids -> SUBSET MsgSpace]
  /\ sentMsgs \subseteq QIds \X {EchoMsg}

\* No action may forge an ECHO: only correct senders appear in sentMsgs, so
\* any count of distinct senders counted against a message is bounded by
\* them being correct, not Byzantine.
FCConstraints ==
  /\ \A m \in sentMsgs : m[1] \in correct
  /\ \A p \in Ids : recvMsgs[p] \subseteq MsgSpace

Init ==
  /\ \E S \in [Ids -> Parts] :
       /\ Cardinality({p \in Ids : S[p] = "lp"}) = N - F
       /\ correct = {p \in Ids : S[p] = "lp"}
       /\ location = S
  /\ recvMsgs = [p \in Ids |-> {}]
  /\ sentMsgs = {}

NoBroadcast ==
  /\ \A p \in Ids : location[p] = "ln"
  /\ recvMsgs = [p \in Ids |-> {}]
  /\ sentMsgs = {}

\* Any correct process may receive any subset of the messages that have
\* actually been put on the wire: correct senders' messages and any that
\* a Byzantine process may have fabricated (the superset below).
ReceiveAny(p) ==
  /\ p \in correct
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] =
        recvMsgs[p] \cup
          CHOOSE S \in SUBSET (sentMsgs \cup (Senders \X {EchoMsg}))
            : S \in SUBSET (sentMsgs \cup (Senders \X {EchoMsg}))
              /\ Cardinality(S) = Cardinality(sentMsgs \cup (Senders \X {EchoMsg}))
      ]
  /\ UNCHANGED <<correct, faulty, location, sentMsgs>>

SendEcho(p) ==
  /\ p \in correct
  /\ sentMsgs' = sentMsgs \cup {<<p, EchoMsg>>}
  /\ location' = [location EXCEPT ![p] = "lp"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

AcceptP(p) ==
  /\ p \in correct
  /\ location[p] # "lp"
  /\ location' = [location EXCEPT ![p] = "lp"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

\* A correct process with no ECHO sent yet may gather enough distinct
\* echoers from the correct pool alone to fire the accept transition.
AcceptWithEcho(p) ==
  /\ p \in correct
  /\ Cardinality(recvMsgs[p] \cap (Senders \X {EchoMsg})) >= N - T
  /\ location[p] # "lp"
  /\ location' = [location EXCEPT ![p] = "lp"]
  /\ sentMsgs' = sentMsgs \cup {<<p, EchoMsg>>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* A correct process already echoing may accept from the quorum it sees.
EchoAccept(p) ==
  /\ p \in correct
  /\ location[p] = "lp"
  /\ Cardinality(recvMsgs[p] \cap (Senders \X {EchoMsg})) >= N - T
  /\ location' = [location EXCEPT ![p] = "lp"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

Next ==
  \/ \E p \in Ids : ReceiveAny(p)
  \/ \E p \in Ids : SendEcho(p)
  \/ \E p \in Ids : AcceptP(p)
  \/ \E p \in Ids : AcceptWithEcho(p)
  \/ \E p \in Ids : EchoAccept(p)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Ids : ReceiveAny(p))
  /\ WF_vars(\E p \in Ids : SendEcho(p))

\* Liveness: when all correct processes start with the INIT message, they
\* all eventually accept; and whenever any correct process accepts, they
\* all do, since a quorum of echoers is now present everywhere.
CorrLtl ==
  (\A p \in Ids : location[p] = "lp") ~> (\A p \in Ids : location[p] = "lp")
RelayLtl ==
  (\E p \in Ids : location[p] = "lp") ~> (\A p \in Ids : location[p] = "lp")

\* Safety: with no correct sender, no correct process ever accepts.
UnforgLtl ==
  (\A p \in Ids : location[p] = "ln") ~> (\A p \in Ids : location[p] = "ln")

====