---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Control locations: InitMsg (process was seeded with the INIT message),
\* DontInit (process was seeded without it), Sent (process has sent ECHO),
\* and Accepted (process has accepted the broadcast).
Locations == { "InitMsg", "DontInit", "Sent", "Accepted" }

VARIABLES correct, faulty, loc, rcvd, sent

vars == <<correct, faulty, loc, rcvd, sent>>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ Cardinality(correct) = (N - F)
  /\ faulty = (1..N) \ correct
  /\ loc \in [1..N -> Locations]
  /\ rcvd \in [1..N -> SUBSET (1..N \cross {"ECHO"})]
  /\ sent \in SUBSET (1..N \cross {"ECHO"})

\* No Byzantine process ever sends: the combined view of all correct
\* processes' received messages is always a subset of what the correct
\* processes actually sent, so no forged identity appears in rcvd.
FCConstraints ==
  \A p \in correct : rcvd[p] \subseteq sent

Init ==
  /\ loc = [p \in 1..N |->
              IF p <= (N - F) THEN "InitMsg" ELSE "DontInit"]
  /\ rcvd = [p \in 1..N |-> {}]
  /\ sent = {}

\* The restricted initial state used to check the no-broadcast case.
NoInitState ==
  /\ loc = [p \in 1..N |-> "DontInit"]
  /\ rcvd = [p \in 1..N |-> {}]
  /\ sent = {}

\* Any process may receive any messages it has not yet heard of; the set
\* consists of everything sent by correct processes plus everything a
\* Byzantine process could forge.
Receive(p) ==
  /\ loc[p] \in {"DontInit", "Sent"}
  /\ \E new \in SUBSET (([1..N -> {"ECHO"}]) \cup
                        ([1..N -> {"ECHO"}] \ {p \in 1..N})):
        rcvd' = [rcvd EXCEPT ![p] = @ \cup new]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* An INIT-receiving correct process accepts immediately and sends ECHO.
InitAccept(p) ==
  /\ loc[p] = "InitMsg"
  /\ loc' = [loc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

\* A not-yet-sending process gathers enough (but not enough to accept)
\* distinct ECHO messages to be allowed to send.
SendEchoNoAccept(p) ==
  /\ loc[p] = "DontInit"
  /\ Cardinality({m \in rcvd[p] : m[2] = "ECHO"}) >= (N - 2 * T)
  /\ Cardinality({m \in rcvd[p] : m[2] = "ECHO"}) < (N - T)
  /\ loc' = [loc EXCEPT ![p] = "Sent"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

\* A not-yet-sending process gathers enough ECHO messages to accept at
\* the same time it sends.
SendEchoAndAccept(p) ==
  /\ loc[p] = "DontInit"
  /\ Cardinality({m \in rcvd[p] : m[2] = "ECHO"}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

\* A process that has already sent may still need to wait for enough ECHO
\* messages before it accepts.
AcceptOnGather(p) ==
  /\ loc[p] = "Sent"
  /\ Cardinality({m \in rcvd[p] : m[2] = "ECHO"}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<correct, faulty, rcvd, sent>>

\* Actions grouped for the weak fairness assumption.
RecvStep == \E p \in correct : Receive(p)
InitStep == \E p \in correct : InitAccept(p)
SendNoAcceptStep == \E p \in correct : SendEchoNoAccept(p)
SendAndAcceptStep == \E p \in correct : SendEchoAndAccept(p)
AcceptStep == \E p \in correct : AcceptOnGather(p)

Next ==
  \/ RecvStep \/ InitStep \/ SendNoAcceptStep \/ SendAndAcceptStep \/ AcceptStep

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RecvStep)
  /\ WF_vars(InitStep)
  /\ WF_vars(SendNoAcceptStep)
  /\ WF_vars(SendAndAcceptStep)
  /\ WF_vars(AcceptStep)

NoBroadInit ==
  \A p \in correct : loc[p] = "DontInit"

NoBroadAccept ==
  \A p \in correct : loc[p] \in {"DontInit", "Sent"}

UnforgLtl == (NoBroadInit) ~> (NoBroadAccept)

CorrLtl == (\A p \in correct : loc[p] = "InitMsg") ~> (\A p \in correct : loc[p] = "Accepted")

RelayLtl == (\E p \in correct : loc[p] = "Accepted") ~> (\A p \in correct : loc[p] = "Accepted")

====