---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, progLoc, recvMsgs, sentMsgs

vars == <<correct, faulty, progLoc, recvMsgs, sentMsgs>>
Msgs == {"ECHO"}
ECHO(i) == <<"ECHO", i>>

InitType == {"noBroadcast", "broadcast"}

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ progLoc \in [1..N -> InitType \cup {"sentEcho", "accepted"}]
  /\ recvMsgs \in [1..N -> SUBSET (Msgs \X (1..N))]
  /\ sentMsgs \subseteq (Msgs \X (1..N))

Init ==
  /\ \E c \in SUBSET (1..N) :
       /\ Cardinality(c) = N - F
       /\ correct = c
       /\ faulty = (1..N) \ c
  /\ progLoc \in [1..N -> InitType]
  /\ recvMsgs = [i \in 1..N |-> {}]
  /\ sentMsgs = {}

InitNoneBroadcast ==
  /\ Init
  /\ \A i \in 1..N : progLoc[i] = "noBroadcast"

Receive(i) ==
  /\ i \in correct
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] = recvMsgs[i] \cup
                    {m \in sentMsgs : m[2] \in correct} \cup
                    (Msgs \X faulty)]
  /\ UNCHANGED <<correct, faulty, progLoc, sentMsgs>>

InitAccept(i) ==
  /\ i \in correct
  /\ progLoc[i] = "broadcast"
  /\ sentMsgs' = sentMsgs \cup {ECHO(i)}
  /\ progLoc' = [progLoc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

GatherEarlyAccept(i) ==
  /\ i \in correct
  /\ progLoc[i] \notin {"accepted", "sentEcho"}
  /\ Cardinality({m \in recvMsgs[i] : m[1] = "ECHO"}) >= N - 2T
  /\ Cardinality({m \in recvMsgs[i] : m[1] = "ECHO"}) < N - T
  /\ sentMsgs' = sentMsgs \cup {ECHO(i)}
  /\ progLoc' = [progLoc EXCEPT ![i] = "sentEcho"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

GatherAccept(i) ==
  /\ i \in correct
  /\ progLoc[i] \notin {"accepted", "sentEcho"}
  /\ Cardinality({m \in recvMsgs[i] : m[1] = "ECHO"}) >= N - T
  /\ sentMsgs' = sentMsgs \cup {ECHO(i)}
  /\ progLoc' = [progLoc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

EchoAccept(i) ==
  /\ i \in correct
  /\ progLoc[i] = "sentEcho"
  /\ Cardinality({m \in recvMsgs[i] : m[1] = "ECHO"}) >= N - T
  /\ progLoc' = [progLoc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

Next ==
  \/ \E i \in 1..N : Receive(i)
  \/ \E i \in 1..N : InitAccept(i)
  \/ \E i \in 1..N : GatherEarlyAccept(i)
  \/ \E i \in 1..N : GatherAccept(i)
  \/ \E i \in 1..N : EchoAccept(i)

Spec == Init /\ [][Next]_vars
Fairness == \A i \in 1..N : WF_vars(Receive(i))

FCConstraints ==
  /\ N > 3 * T
  /\ N \notin Nat
  /\ T \in Nat
  /\ F \in Nat
  /\ T >= F
  /\ F >= 0

UnforgLtl == (\A i \in correct : progLoc[i] = "noBroadcast")
              ~> (\A i \in correct : progLoc[i] = "broadcast")
CorrLtl == (\A i \in correct : progLoc[i] = "broadcast")
             ~> (\A i \in correct : progLoc[i] = "accepted")
RelayLtl == (\E i \in correct : progLoc[i] = "accepted")
              ~> (\A i \in correct : progLoc[i] = "accepted")

====