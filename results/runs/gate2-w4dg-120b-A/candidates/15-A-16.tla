---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N \in Nat /\ T \in Nat /\ F \in Nat
       /\ N > 3 * T
       /\ T >= F
       /\ F >= 0

VARIABLES correct, faulty, loc, inbox, sent

vars == <<correct, faulty, loc, inbox, sent>>

Locations == {"init", "nobroadcast", "echoed", "accepted"}

\* A received message is a pair of its sender and its type; only ECHO is ever sent.
MsgTypes == {"ECHO"}
Messages == {<<i, mtype>> \in 1..N \X MsgTypes : i \in 1..N}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Locations]
  /\ inbox \in [1..N -> SUBSET Messages]
  /\ sent \subseteq Messages

FCConstraints ==
  /\ loc \in [1..N -> Locations]
  /\ inbox \in [1..N -> SUBSET Messages]

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ sent = {}
  /\ \E s \in {"init", "nobroadcast"} :
       /\ loc = [i \in 1..N |-> s]
       /\ inbox = [i \in 1..N |-> {}]

\* A correct process may receive a set of new messages, from correct senders
\* and from faulty ones combined, at any time -- messages can be arbitrarily
\* reordered and delayed, so this is the only nondeterministic step.
Receive ==
  /\ \E i \in correct :
       /\ \E mset \in SUBSET (sent \cup Messages) :
            /\ inbox' = [inbox EXCEPT ![i] = inbox[i] \cup mset]
            /\ UNCHANGED <<correct, faulty, loc, sent>>

\* A process that got the broadcaster's INIT message accepts immediately.
BroadcastStart ==
  /\ \E i \in correct :
       /\ loc[i] = "init"
       /\ loc' = [loc EXCEPT ![i] = "accepted"]
       /\ sent' = sent \cup {<<i, "ECHO">>}
       /\ UNCHANGED <<correct, faulty, inbox>>

\* A process that has not yet sent ECHO receives enough, but not a quorum, so
\* it sends ECHO and waits.
EchoStep ==
  /\ \E i \in correct :
       /\ loc[i] \in {"nobroadcast", "init"}
       /\ Cardinality({msg \in inbox[i] : msg[2] = "ECHO"}) >= N - 2 * T
       /\ Cardinality({msg \in inbox[i] : msg[2] = "ECHO"}) < N - T
       /\ loc' = [loc EXCEPT ![i] = "echoed"]
       /\ sent' = sent \cup {<<i, "ECHO">>}
       /\ UNCHANGED <<correct, faulty, inbox>>

\* A process that has not yet sent ECHO receives a quorum and accepts.
QuorumEcho ==
  /\ \E i \in correct :
       /\ loc[i] \in {"nobroadcast", "init"}
       /\ Cardinality({msg \in inbox[i] : msg[2] = "ECHO"}) >= N - T
       /\ loc' = [loc EXCEPT ![i] = "accepted"]
       /\ sent' = sent \cup {<<i, "ECHO">>}
       /\ UNCHANGED <<correct, faulty, inbox>>

\* A process that already sent ECHO receives a quorum and accepts.
QuorumAccept ==
  /\ \E i \in correct :
       /\ loc[i] \in {"echoed"}
       /\ Cardinality({msg \in inbox[i] : msg[2] = "ECHO"}) >= N - T
       /\ loc' = [loc EXCEPT ![i] = "accepted"]
       /\ UNCHANGED <<correct, faulty, inbox, sent>>

Next ==
  \/ Receive
  \/ BroadcastStart
  \/ EchoStep
  \/ QuorumEcho
  \/ QuorumAccept

InitFair == Init /\ Receive
FairStep == Receive /\ BroadcastStart /\ EchoStep /\ QuorumEcho /\ QuorumAccept

Spec == InitFair /\ [][Next]_vars
        /\ WF_vars(InitFair) /\ SF_vars(FairStep)

\* If no correct process ever broadcasts, no correct process accepts.
UnforgLtl == (\A i \in correct : loc[i] # "init") ~> (\A i \in correct : loc[i] = "accepted")

CorrLtl == (\A i \in correct : loc[i] = "init") ~> (\A i \in correct : loc[i] = "accepted")

RelayLtl == (\E i \in correct : loc[i] = "accepted") ~> (\A i \in correct : loc[i] = "accepted")

====