---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N \in Nat /\ N >= 4
       /\ T \in Nat /\ T >= 1
       /\ F \in Nat /\ F >= 0
       /\ N > 3 * T
       /\ T >= F

Nodes == 0 .. (N - 1)
ECHO == "echo"
NoMsg == [from |-> 0, kind |-> "none"]
NoInit == 0
GotInit == 1
SentEcho == 2
Accepted == 3

VARIABLES correct, faulty, loc, recvd, sent
vars == <<correct, faulty, loc, recvd, sent>>

TypeOK ==
  /\ correct \subseteq Nodes
  /\ faulty \subseteq Nodes
  /\ loc \in [Nodes -> {NoInit, GotInit, SentEcho, Accepted}]
  /\ recvd \in [Nodes -> SUBSET [from: Nodes, kind: {ECHO}]]
  /\ sent \subseteq [from: Nodes, kind: {ECHO}]

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = Nodes
  /\ sent \subseteq [from |-> Nodes, kind |-> {ECHO}]
  /\ \A n \in Nodes : Cardinality(recvd[n]) <= N

Init ==
  \E c \in SUBSET Nodes :
    /\ Cardinality(c) = N - F
    /\ correct = c
    /\ faulty = Nodes \ c
    /\ \E initLoc \in {NoInit, GotInit} :
         loc = [n \in Nodes |-> initLoc]
    /\ recvd = [n \in Nodes |-> {}]
    /\ sent = {}

InitNoBroadcast ==
  \E c \in SUBSET Nodes :
    /\ Cardinality(c) = N - F
    /\ correct = c
    /\ faulty = Nodes \ c
    /\ loc = [n \in Nodes |-> NoInit]
    /\ recvd = [n \in Nodes |-> {}]
    /\ sent = {}

Receive(n, msgs) ==
  /\ loc[n] # Accepted
  /\ msgs \subseteq ({m \in [from : correct, kind : {ECHO}] : m \notin recvd[n]}
                     \cup [from |-> faulty, kind |-> ECHO])
  /\ recvd' = [recvd EXCEPT ![n] = @ \cup msgs]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

SendEcho(n) ==
  /\ loc[n] = GotInit
  /\ loc' = [loc EXCEPT ![n] = Accepted]
  /\ sent' = sent \cup {[from |-> n, kind |-> ECHO]}
  /\ UNCHANGED <<correct, faulty, recvd>>

EchoAndAct(n) ==
  /\ loc[n] = NoInit
  /\ Cardinality(recvd[n]) >= N - 2 * T
  /\ Cardinality(recvd[n]) < N - T
  /\ loc' = [loc EXCEPT ![n] = SentEcho]
  /\ sent' = sent \cup {[from |-> n, kind |-> ECHO]}
  /\ UNCHANGED <<correct, faulty, recvd>>

EchoAndAccept(n) ==
  /\ loc[n] \in {NoInit, SentEcho}
  /\ Cardinality(recvd[n]) >= N - T
  /\ loc' = [loc EXCEPT ![n] = Accepted]
  /\ sent' = sent \cup {[from |-> n, kind |-> ECHO]}
  /\ UNCHANGED <<correct, faulty, recvd>>

AcceptNow(n) ==
  /\ loc[n] = SentEcho
  /\ Cardinality(recvd[n]) >= N - T
  /\ loc' = [loc EXCEPT ![n] = Accepted]
  /\ UNCHANGED <<correct, faulty, recvd, sent>>

Next ==
  \/ \E n \in Nodes, msgs \in SUBSET [from : Nodes, kind : {ECHO}] :
       Receive(n, msgs)
  \/ \E n \in Nodes : SendEcho(n)
  \/ \E n \in Nodes : EchoAndAct(n)
  \/ \E n \in Nodes : EchoAndAccept(n)
  \/ \E n \in Nodes : AcceptNow(n)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E n \in Nodes, msgs \in SUBSET [from : Nodes, kind : {ECHO}] : Receive(n, msgs))
        /\ WF_vars(\E n \in Nodes : EchoAndAct(n))
        /\ WF_vars(\E n \in Nodes : EchoAndAccept(n))
        /\ WF_vars(\E n \in Nodes : AcceptNow(n))

UnforgLtl == (LocAll = NoInit) ~> (LocAll = Accepted)
CorrLtl == (LocAll = GotInit) ~> (LocAll = Accepted)
RelayLtl == (LocSome = Accepted) ~> (LocAll = Accepted)

LocAll == \A n \in Nodes : loc[n]
LocSome == CHOOSE n \in Nodes : TRUE

====