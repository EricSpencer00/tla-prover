---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

CorrectProc == "correct"
FaultyProc == "faulty"
NoProc == "none"
Msgs == {"ECHO"}
NActions == {"none", "init", "noinit", "sent", "adopted"}

VARIABLES corrSet, procClass, ctrl, inbox, byzOut

vars == <<corrSet, procClass, ctrl, inbox, byzOut>>

\* State of a process: which group it belongs to (correct/faulty), which
\* control location of the broadcast protocol it is in, and what messages it
\* has already consumed. byzOut tracks the arbitrary traffic Byzantine
\* processes may inject on the network.
TypeOK ==
  /\ corrSet \subseteq 1..N
  /\ procClass \in [1..N -> {"correct", "faulty"}]
  /\ ctrl \in [1..N -> NActions]
  /\ inbox \in [1..N -> SUBSET (1..N \X Msgs)]
  /\ byzOut \subseteq 1..N

Init ==
  /\ corrSet = {p \in 1..N : Cardinality(corrSet) < N - F}
  /\ procClass = [p \in 1..N |-> IF p \in corrSet THEN CorrectProc ELSE FaultyProc]
  /\ ctrl = [p \in 1..N |-> IF p \in corrSet THEN "init" ELSE "noinit"]
  /\ inbox = [p \in 1..N |-> {}]
  /\ byzOut = {}

InitRestricted ==
  /\ corrSet = {p \in 1..N : Cardinality(corrSet) < N - F}
  /\ procClass = [p \in 1..N |-> IF p \in corrSet THEN CorrectProc ELSE FaultyProc]
  /\ ctrl = [p \in 1..N |-> "noinit"]
  /\ inbox = [p \in 1..N |-> {}]
  /\ byzOut = {}

\* A correct process receives any subset of all messages sent by correct
\* processes, together with arbitrary traffic from the Byzantine group.
Receive(p, mset) ==
  /\ procClass[p] = CorrectProc
  /\ ctrl[p] \notin {"adopted", "sent"}
  /\ mset \subseteq {q \in 1..N : procClass[q] = CorrectProc} \X Msgs \cup (byzOut \X Msgs)
  /\ inbox' = [inbox EXCEPT ![p] = mset]
  /\ ctrl' = [ctrl EXCEPT ![p] = IF ctrl[p] = "init" THEN "adopted" ELSE "sent"]
  /\ UNCHANGED <<corrSet, procClass, byzOut>>

\* A correct process that was the broadcaster sends the mandatory ECHO.
EchoBroadcast(p) ==
  /\ procClass[p] = CorrectProc
  /\ ctrl[p] = "init"
  /\ ctrl' = [ctrl EXCEPT ![p] = "adopted"]
  /\ byzOut' = byzOut \cup {p}
  /\ UNCHANGED <<corrSet, procClass, inbox>>

\* A correct process that received enough ECHO's (but not yet a majority)
\* sends its own ECHO without adopting the broadcast.
EchoRelay(p) ==
  /\ procClass[p] = CorrectProc
  /\ ctrl[p] = "sent"
  /\ Cardinality({q \in inbox[p] : q[2] = "ECHO"}) >= N - 2 * T
  /\ Cardinality({q \in inbox[p] : q[2] = "ECHO"}) < N - T
  /\ ctrl' = [ctrl EXCEPT ![p] = "sent"]
  /\ byzOut' = byzOut \cup {p}
  /\ UNCHANGED <<corrSet, procClass, inbox>>

\* A correct process that received a majority of ECHO's sends its own
\* ECHO and adopts the broadcast in the same step.
EchoAdopt(p) ==
  /\ procClass[p] = CorrectProc
  /\ ctrl[p] = "sent"
  /\ Cardinality({q \in inbox[p] : q[2] = "ECHO"}) >= N - T
  /\ ctrl' = [ctrl EXCEPT ![p] = "adopted"]
  /\ byzOut' = byzOut \cup {p}
  /\ UNCHANGED <<corrSet, procClass, inbox>>

\* A correct process that already sent its ECHO adopts the broadcast once
\* a majority of ECHO's has accumulated.
Adopt(p) ==
  /\ procClass[p] = CorrectProc
  /\ ctrl[p] = "sent"
  /\ Cardinality({q \in inbox[p] : q[2] = "ECHO"}) >= N - T
  /\ ctrl' = [ctrl EXCEPT ![p] = "adopted"]
  /\ UNCHANGED <<corrSet, procClass, inbox, byzOut>>

Next ==
  \/ \E p \in 1..N, mset \in SUBSET (1..N \X Msgs) : Receive(p, mset)
  \/ \E p \in 1..N : EchoBroadcast(p)
  \/ \E p \in 1..N : EchoRelay(p)
  \/ \E p \in 1..N : EchoAdopt(p)
  \/ \E p \in 1..N : Adopt(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : EchoRelay(p) \/ EchoAdopt(p) \/ Adopt(p))

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ Cardinality(corrSet) = N - F

CorrLtl == \A p \in 1..N : (procClass[p] = CorrectProc /\ ctrl[p] = "init") ~> (procClass[p] = CorrectProc /\ ctrl[p] = "adopted")

RelayLtl == <>(\E p \in 1..N : procClass[p] = CorrectProc /\ ctrl[p] = "adopted") ~> (\A p \in 1..N : procClass[p] = CorrectProc => ctrl[p] = "adopted")

UnforgLtl == (\A p \in 1..N : procClass[p] = CorrectProc => ctrl[p] # "init") ~> (\A p \in 1..N : procClass[p] = CorrectProc => ctrl[p] = "adopted")

====