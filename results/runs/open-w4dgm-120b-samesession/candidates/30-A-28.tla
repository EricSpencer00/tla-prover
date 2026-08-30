---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ 2 * T < N
       /\ F \in Nat /\ F <= T
       /\ Values \subset Nat /\ Bottom \notin Values

Dwellers == 0 .. (N - 1)
Bump(i) == IF i = N - 1 THEN 0 ELSE i + 1

VARIABLES loc, view, propose, estimate, decided, crashed, sent, recvd

vars == <<loc, view, propose, estimate, decided, crashed, sent, recvd>>

Onward(d) == d[Bump(d)]

Broadcast(m) == sent \cup {m}
Refresh(d, m) == IF d[m.sender] = Bottom
                 THEN [d EXCEPT ![m.sender] = m.val]
                 ELSE d
Seen(m) == \E r \in recvd[m.recver] : r.val = m.val /\ r.sender = m.sender

TypeOK ==
  /\ loc \in [Dwellers -> {"bcast1", "wait1", "prep", "bcast2", "wait2", "done", "crashed", "choosing"}]
  /\ view \in [Dwellers -> [Dwellers -> Values \cup {Bottom}]]
  /\ propose \in [Dwellers -> Values]
  /\ estimate \in [Dwellers -> Values \cup {Bottom}]
  /\ decided \in [Dwellers -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [sender: Dwellers, val: Values \cup {Bottom}, kind: {"p1", "p2"}]
  /\ recvd \in [Dwellers -> SUBSET [sender: Dwellers, val: Values \cup {Bottom}, kind: {"p1", "p2"}, recver: Dwellers]]

Init ==
  /\ loc = [i \in Dwellers |-> "bcast1"]
  /\ view = [i \in Dwellers |-> [j \in Dwellers |-> Bottom]]
  /\ propose \in [Dwellers -> Values]
  /\ estimate = [i \in Dwellers |-> Bottom]
  /\ decided = [i \in Dwellers |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [i \in Dwellers |-> {}]

BumpWhole(d) == [i \in Dwellers |-> Onward(d[i])]

BroadcastP1(i) ==
  /\ loc[i] = "bcast1"
  /\ sent' = Broadcast([sender |-> i, val |-> propose[i], kind |-> "p1"])
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recvd>>

ReceiveP1(i, m) ==
  /\ loc[i] = "wait1"
  /\ m.kind = "p1"
  /\ ~Seen(m)
  /\ recvd' = [recvd EXCEPT ![i] = @ \cup {[m EXCEPT !.recver = i]}]
  /\ view' = [view EXCEPT ![i] = Refresh(@, m)]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashed, sent>>

Transition1(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality({m \in recvd[i] : m.kind = "p1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE e \in Values : \A j \in Dwellers : view[i][j] <= e]
  /\ loc' = "bcast2"
  /\ UNCHANGED <<view, propose, decided, crashed, sent, recvd>>

BroadcastP2(i) ==
  /\ loc[i] = "bcast2"
  /\ sent' = Broadcast([sender |-> i, val |-> propose[i], kind |-> "p2"])
  /\ loc' = "wait2"
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recvd>>

ReceiveP2(i, m) ==
  /\ loc[i] = "wait2"
  /\ m.kind = "p2"
  /\ ~Seen(m)
  /\ recvd' = [recvd EXCEPT ![i] = @ \cup {[m EXCEPT !.recver = i]}]
  /\ view' = [view EXCEPT ![i] = Refresh(@, m)]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashed, sent>>

DecisionBound(e, i) == Cardinality({m \in recvd[i] : m.kind = "p2" /\ m.val = e}) >= N - T

Transition2(i) ==
  /\ loc[i] = "wait2"
  /\ \E e \in Values : DecisionBound(e, i)
  /\ decided' = [decided EXCEPT ![i] = CHOOSE e \in Values : DecisionBound(e, i)]
  /\ loc' = "done"
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recvd>>

Choose(i) ==
  /\ loc[i] = "wait2"
  /\ \A j \in Dwellers : Cardinality(recvd[i]) = N
  /\ \A e \in Values : ~DecisionBound(e, i)
  /\ loc' = "choosing"
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, sent, recvd>>

DecideChosen(i) ==
  /\ loc[i] = "choosing"
  /\ decided' = [decided EXCEPT ![i] = CHOOSE e \in Values : \E j \in Dwellers : view[i][j] = e]
  /\ loc' = "done"
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recvd>>

Crash(i) ==
  /\ loc[i] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decided, sent, recvd>>

Next ==
  \E i \in Dwellers :
    \/ BroadcastP1(i)
    \/ BroadcastP2(i)
    \/ Transition1(i)
    \/ Transition2(i)
    \/ Choose(i)
    \/ DecideChosen(i)
    \/ Crash(i)
    \/ \E m \in sent : ReceiveP1(i, m) \/ ReceiveP2(i, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(BumpWhole(view))
  /\ WF_vars(BumpWhole(loc))
  /\ WF_vars(BumpWhole(recvd))

Agreement ==
  \A i, j \in Dwellers : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Validity ==
  \A i \in Dwellers : (decided[i] # Bottom) => \E j \in Dwellers : propose[j] = decided[i]

Terminating == \A i \in Dwellers : loc[i] \in {"done", "crashed"}

ConditionalTermination ==
  \E i \in Dwellers : (decided[i] # Bottom /\ decided[i] = CHOOSE e \in Values : \A j \in Dwellers : propose[j] <= e) \/ Terminating

Properties == Terminating /\ ConditionalTermination

====