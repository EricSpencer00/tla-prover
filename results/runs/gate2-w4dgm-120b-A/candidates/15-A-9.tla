---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent
vars == <<correct, faulty, pc, recv, sent>>

Procs == 0..(N - 1)
Echoes == {<<"ECHO", p>> : p \in Procs}

InitPcs == {"init", "noinit"}
StagePcs == {"sentyes", "sentno", "sentyesaccept", "sentnoaccept"}

TypeOK ==
  /\ correct \subseteq Procs
  /\ Cardinality(correct) = (N - F)
  /\ faulty = Procs \ correct
  /\ pc \in [Procs -> StagePcs]
  /\ recv \in [Procs -> SUBSET Echoes]
  /\ sent \subseteq Echoes

Init ==
  /\ \E g \in [Procs -> InitPcs] :
        /\ correct = {p \in Procs : g[p] = "init"}
        /\ pc = [p \in Procs |-> (IF g[p] = "init" THEN "sentyes" ELSE "sentno")]
        /\ recv = [p \in Procs |-> {}]
  /\ sent = {}
  /\ faulty = Procs \ correct

NoBroadInit ==
  /\ correct = Procs
  /\ \A p \in Procs : pc[p] = "sentno"
  /\ recv = [p \in Procs |-> {}]
  /\ sent = {}
  /\ faulty = {}

ReceiveMsgs(p) ==
  /\ pc[p] \in {"sentyes", "sentno"}
  /\ \E m \in [Echoes -> BOOLEAN] :
        /\ m \in recv[p] => m \in sent
        /\ \A e \in Echoes : (e \in recv[p] <=> m[e])
  /\ \E q \in Procs :
        /\ {\<<<<"ECHO", q>>\}} \subseteq sent
        /\ pc[q] \in {"sentyesaccept", "sentnoaccept"}

SendEcho(p) ==
  /\ pc[p] \in {"sentyes", "sentno"}
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ pc' = [pc EXCEPT ![p] = "sentyesaccept"]
  /\ UNCHANGED <<correct, faulty, recv>>

EchoCount(p) ==
  {q \in Procs : <<"ECHO", q>> \in recv[p]}

BroadcastStage(p) ==
  /\ pc[p] \in {"sentyes", "sentno"}
  /\ Cardinality(EchoCount(p)) >= (N - 2 * T)
  /\ Cardinality(EchoCount(p)) < (N - T)
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "sentyes" THEN "sentyesaccept" ELSE "sentnoaccept"]
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptStage(p) ==
  /\ pc[p] \in {"sentyes", "sentno"}
  /\ Cardinality(EchoCount(p)) >= (N - T)
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "sentyes" THEN "sentyesaccept" ELSE "sentnoaccept"]
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptAfterEcho(p) ==
  /\ pc[p] \in {"sentyesaccept", "sentnoaccept"}
  /\ Cardinality(EchoCount(p)) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "sentyesaccept" THEN "sentyesaccept" ELSE "sentnoaccept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \E p \in Procs :
    \/ ReceiveMsgs(p)
    \/ SendEcho(p)
    \/ BroadcastStage(p)
    \/ AcceptStage(p)
    \/ AcceptAfterEcho(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs : WF_vars(ReceiveMsgs(p))
  /\ \A p \in Procs : WF_vars(BroadcastStage(p))
  /\ \A p \in Procs : WF_vars(AcceptStage(p))
  /\ \A p \in Procs : WF_vars(AcceptAfterEcho(p))

Accepting(p) == pc[p] \in {"sentyesaccept", "sentnoaccept"}

CorrLtl == \A p \in correct : (pc[p] = "sentyes") ~> Accepting(p)

RelayLtl == (\E p \in correct : Accepting(p)) ~> (\A p \in correct : Accepting(p))

FCConstraints ==
  /\ N > (3 * T)
  /\ T >= F
  /\ F >= 0

UnforgLtl ==
  /\ NoBroadInit
  /\ (\A p \in correct : pc[p] # "sentyesaccept")
====