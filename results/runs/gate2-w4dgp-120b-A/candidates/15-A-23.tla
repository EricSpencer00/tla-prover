---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process that has received the broadcaster's INIT message is in the
\* "broadcast-received" state; a process that has not is in the
\* "non-broadcast" state. Each correct process eventually sends a single
\* ECHO message to all and then accepts once it has collected enough
\* distinct ECHO messages from others.

Correct \in SUBSET (1..N)
Faulty \in SUBSET (1..N)
State \in [1..N -> {"init", "non", "echoed", "done"}]
Received \in [1..N -> SUBSET [sender: 1..N, kind: {"echo"}]]
SendLog \subseteq (1..N) \X {"echo"}

InitSet \in {"both", "none"}

TypeOK ==
  /\ Correct \cup Faulty = (1..N)
  /\ Correct \cap Faulty = {}
  /\ N > 3 * T /\ T >= F /\ F >= 0
  /\ State \in [1..N -> {"init", "non", "echoed", "done"}]
  /\ Received \in [1..N -> SUBSET [sender: 1..N, kind: {"echo"}]]
  /\ SendLog \subseteq (1..N) \X {"echo"}

Init ==
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ \E st \in {"init", "non"} :
       (\A p \in (1..N) : State[p] = st)
  /\ \A p \in (1..N) : Received[p] = {}
  /\ \A p \in (1..N) : SendLog \cap ({p} \X {"echo"}) = {}
  /\ InitSet = "both"

InitNone ==
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ \A p \in (1..N) : State[p] = "non"
  /\ \A p \in (1..N) : Received[p] = {}
  /\ \A p \in (1..N) : SendLog \cap ({p} \X {"echo"}) = {}
  /\ InitSet = "none"

\* Correct processes receive arbitrarily many messages, including any
\* messages that Byzantine processes might forge.
Receive(p) ==
  /\ p \in Correct
  /\ State[p] # "done"
  /\ \E m \subseteq (SendLog \cup (Faulty \X {"echo"}) \ {p} \X {"echo"}) :
       Received' = [Received EXCEPT ![p] = Received[p] \cup m]
  /\ UNCHANGED <<Correct, Faulty, State, SendLog, InitSet>>

\* A process that had the broadcast to begin with accepts immediately
\* and sends its own ECHO message.
InitBroadcast(p) ==
  /\ p \in Correct
  /\ State[p] = "init"
  /\ SendLog' = SendLog \cup ({p} \X {"echo"})
  /\ State' = [State EXCEPT ![p] = "done"]
  /\ UNCHANGED <<Correct, Faulty, Received, InitSet>>

\* With only a minority of ECHO messages collected (< quorum), a correct
\* process may still send its ECHO message but must not accept yet.
EchoWeak(p) ==
  /\ p \in Correct
  /\ State[p] = "non"
  /\ Cardinality({q \in (1..N) : [q, "echo"] \in Received[p]}) >= N - 2 * T
  /\ Cardinality({q \in (1..N) : [q, "echo"] \in Received[p]}) < N - T
  /\ SendLog' = SendLog \cup ({p} \X {"echo"})
  /\ State' = [State EXCEPT ![p] = "echoed"]
  /\ UNCHANGED <<Correct, Faulty, Received, InitSet>>

\* With a quorum of ECHO messages collected, the process accepts.
EchoStrong(p) ==
  /\ p \in Correct
  /\ State[p] \in {"non", "echoed"}
  /\ Cardinality({q \in (1..N) : [q, "echo"] \in Received[p]}) >= N - T
  /\ SendLog' = SendLog \cup ({p} \X {"echo"})
  /\ State' = [State EXCEPT ![p] = "done"]
  /\ UNCHANGED <<Correct, Faulty, Received, InitSet>>

RelayDone(p) ==
  /\ p \in Correct
  /\ State[p] = "echoed"
  /\ Cardinality({q \in (1..N) : [q, "echo"] \in Received[p]}) >= N - T
  /\ State' = [State EXCEPT ![p] = "done"]
  /\ UNCHANGED <<Correct, Faulty, Received, SendLog, InitSet>>

Done ==
  /\ \A p \in (1..N) : State[p] = "done"
  /\ UNCHANGED <<Correct, Faulty, State, Received, SendLog, InitSet>>

WeakStep ==
  \/ \E p \in (1..N) : Receive(p)
  \/ \E p \in (1..N) : InitBroadcast(p)
  \/ \E p \in (1..N) : EchoWeak(p)
  \/ \E p \in (1..N) : EchoStrong(p)
  \/ \E p \in (1..N) : RelayDone(p)
  \/ Done

Next ==
  \/ WeakStep
  \/ \E p \in (1..N) : Receive(p)

Spec ==
  /\ Init \/ InitNone
  /\ [][Next]_<<Correct, Faulty, State, Received, SendLog, InitSet>>
  /\ WF_vars(WeakStep)

FCConstraints ==
  /\ InitSet = "both" => (\A p \in Correct : State[p] = "done")
  /\ InitSet = "none" => (\A p \in Correct : State[p] # "done")

CorrLtl == InitSet = "both" ~> (\A p \in Correct : State[p] = "done")
RelayLtl == (\E p \in Correct : State[p] = "done") ~> (\A p \in Correct : State[p] = "done")
UnforgLtl == InitSet = "none" ~> (\A p \in Correct : State[p] # "done")
====