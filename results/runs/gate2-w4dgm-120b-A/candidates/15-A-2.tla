---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F

(* MsgType is the fixed set of message kinds the protocol recognises. *)
MsgType == {"ECHO"}

VARIABLES correct, faulty, pc, recvSet, sentSet

vars == << correct, faulty, pc, recvSet, sentSet >>

Locations == {"init0", "init1", "sent", "accepted"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> Locations]
  /\ recvSet \in [1..N -> SUBSET (1..N \X MsgType)]
  /\ sentSet \subseteq (1..N \X MsgType)

Init ==
  /\ correct = CHOOSE c \in SUBSET (1..N) : Cardinality(c) = N - F
  /\ pc = [i \in 1..N |-> IF i \in correct THEN "init1" ELSE "init0"]
  /\ recvSet = [i \in 1..N |-> {}]
  /\ sentSet = {}

InitNoBroadcast ==
  /\ correct = CHOOSE c \in SUBSET (1..N) : Cardinality(c) = N - F
  /\ pc = [i \in 1..N |-> "init0"]
  /\ recvSet = [i \in 1..N |-> {}]
  /\ sentSet = {}

\* Actions that model a correct process receiving a batch of new messages
\* from both correct senders and Byzantine (faulty) ones.
Receive(i) ==
  \E msgs \in SUBSET (sentSet \cup (faulty \X MsgType)) :
    /\ i \in correct
    /\ pc[i] \in {"init0", "init1", "sent"}
    /\ msgs # {}
    /\ recvSet' = [recvSet EXCEPT ![i] = @ \cup msgs]
    /\ UNCHANGED << correct, faulty, pc, sentSet >>

BroadcastInit(i) ==
  /\ i \in correct
  /\ pc[i] = "init1"
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentSet' = sentSet \cup {<< i, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, recvSet >>

\* A correct process that has not yet sent ECHO reacts to a quorum below the
\* accept threshold by sending ECHO but not yet accepting.
SendEchoPre(i) ==
  /\ i \in correct
  /\ pc[i] = "init0"
  /\ Cardinality({s \in 1..N : << s, "ECHO" >> \in recvSet[i]}) >= N - 2 * T
  /\ Cardinality({s \in 1..N : << s, "ECHO" >> \in recvSet[i]}) < N - T
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ sentSet' = sentSet \cup {<< i, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, recvSet >>

\* A correct process that has not yet sent ECHO reacts to a strong quorum by
\* sending ECHO and immediately accepting.
SendEchoAccept(i) ==
  /\ i \in correct
  /\ pc[i] \in {"init0", "sent"}
  /\ Cardinality({s \in 1..N : << s, "ECHO" >> \in recvSet[i]}) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentSet' = sentSet \cup {<< i, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, recvSet >>

RecvEcho(i) ==
  /\ i \in correct
  /\ pc[i] = "sent"
  /\ Cardinality({s \in 1..N : << s, "ECHO" >> \in recvSet[i]}) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED << correct, faulty, recvSet, sentSet >>

Next ==
  \/ Init \/ InitNoBroadcast
  \/ \E i \in 1..N : Receive(i)
  \/ \E i \in 1..N : BroadcastInit(i)
  \/ \E i \in 1..N : SendEchoPre(i)
  \/ \E i \in 1..N : SendEchoAccept(i)
  \/ \E i \in 1..N : RecvEcho(i)

Spec == Init /\ [][Next]_vars
        /\ (\A i \in 1..N : WF_vars(Receive(i)))
        /\ (\A i \in 1..N : SF_vars(SendEchoPre(i)))
        /\ (\A i \in 1..N : SF_vars(SendEchoAccept(i)))
        /\ (\A i \in 1..N : WF_vars(RecvEcho(i)))

(* No broadcast, no acceptance: if no correct process ever broadcasts an *)
(* ECHO (an empty broadcast round), no correct process reaches acceptance. *)
FCConstraints == \A i \in correct : (pc[i] = "accepted") => (sentSet # {})

CorrLtl == \A i \in correct : (pc[i] = "init1") ~> (pc[i] = "accepted")
RelayLtl == (\E i \in correct : pc[i] = "accepted") ~> (\A i \in correct : pc[i] = "accepted")
UnforgLtl == (\A i \in correct : pc[i] = "init0") ~> (\A i \in correct : pc[i] # "accepted")

====