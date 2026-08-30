---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, recvMsgs, sentMsgs

vars == <<correct, faulty, loc, recvMsgs, sentMsgs>>

Bloxes == 0..(N - 1)
Msgs == [sender : Bloxes, typ : {"ECHO"}]
Locations == {"initrecv", "nonrecv", "sentEcho", "accepted"}

InitLoc(i) == IF i < N - F THEN "initrecv" ELSE "nonrecv"

RECURSIVE SumCount(_, _)
SumCount(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumCount(f, S \ {x})

EchoSenders(i) == { m.sender : m \in recvMsgs[i] : m.typ = "ECHO" }

Init ==
    /\ correct = {0, 1, 2, 3}
    /\ faulty = {}
    /\ loc = [i \in Bloxes |-> InitLoc(i)]
    /\ recvMsgs = [i \in Bloxes |-> {}]
    /\ sentMsgs = {}

InitRestricted ==
    /\ correct = {0, 1, 2, 3}
    /\ faulty = {}
    /\ loc = [i \in Bloxes |-> "nonrecv"]
    /\ recvMsgs = [i \in Bloxes |-> {}]
    /\ sentMsgs = {}

DropAll(m) == {[sender |-> m.sender, typ |-> t] : t \in {"ECHO"}}
CrashedSend(i) == [sender |-> i, typ |-> "ECHO"]

Receive(i) ==
    /\ \E S \in SUBSET (sentMsgs \cup DropAll(CrashedSend(i))) :
        recvMsgs' = [recvMsgs EXCEPT ![i] = recvMsgs[i] \cup S]
    /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

SendEcho(i) ==
    /\ i \in correct
    /\ loc[i] = "initrecv"
    /\ loc' = [loc EXCEPT ![i] = "sentEcho"]
    /\ sentMsgs' = sentMsgs \cup {CrashedSend(i)}
    /\ UNCHANGED <<correct, faulty, recvMsgs>>

SendEchoOnThreshold(i) ==
    /\ i \in correct
    /\ loc[i] = "nonrecv"
    /\ Cardinality(EchoSenders(i)) >= N - 2 * T
    /\ loc' = [loc EXCEPT ![i] = "sentEcho"]
    /\ sentMsgs' = sentMsgs \cup {CrashedSend(i)}
    /\ UNCHANGED <<correct, faulty, recvMsgs>>

AcceptOnThreshold(i) ==
    /\ i \in correct
    /\ loc[i] # "accepted"
    /\ Cardinality(EchoSenders(i)) >= N - T
    /\ loc' = [loc EXCEPT ![i] = "accepted"]
    /\ sentMsgs' = IF loc[i] = "nonrecv" THEN sentMsgs \cup {CrashedSend(i)} ELSE sentMsgs
    /\ UNCHANGED <<correct, faulty, recvMsgs>>

RecvAct(i) == Receive(i) \/ SendEcho(i) \/ SendEchoOnThreshold(i) \/ AcceptOnThreshold(i)

Next ==
    \/ Init \/ InitRestricted
    \/ \E i \in Bloxes : RecvAct(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A i \in Bloxes : WF_vars(RecvAct(i))

TypeOK ==
    /\ correct \subseteq Bloxes
    /\ faulty \subseteq Bloxes
    /\ loc \in [Bloxes -> Locations]
    /\ recvMsgs \in [Bloxes -> SUBSET Msgs]
    /\ sentMsgs \subseteq Msgs

FCConstraints ==
    /\ correct \cup faulty = Bloxes
    /\ correct \cap faulty = {}
    /\ Cardinality(correct) = N - F
    /\ SumCount([i \in Bloxes |-> IF loc[i] = "accepted" THEN 1 ELSE 0], Bloxes) <= Cardinality(correct)

CorrLtl == <>(\A i \in correct : loc[i] = "accepted")
RelayLtl == (\E i \in correct : loc[i] = "accepted") ~> (\A i \in correct : loc[i] = "accepted")
UnforgLtl == (\A i \in correct : loc[i] = "nonrecv") ~> (\A i \in correct : loc[i] # "accepted")

====