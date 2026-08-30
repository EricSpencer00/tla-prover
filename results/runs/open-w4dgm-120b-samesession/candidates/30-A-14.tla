---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, inbox, prop, estimate, decided, crashed, sent, recv
vars == <<loc, inbox, prop, estimate, decided, crashed, sent, recv>>

\* The phase-1 and phase-2 phases are distinguished by msgType, and a process only
\* ever acts on a message whose type matches the phase it is currently in.
MsgTypes == {"phase1", "phase2"}
\* Inequality allows an arbitrary total order on the value set; Bottom is the
\* sentinel filling an as-yet-unknown entry of the view matrix.
Orders == {u \in Values \X Values : u[1] # u[2]}
Msgs == [type : MsgTypes, val : Values, sender : 0 .. N - 1] \X Orders

Bump(v, S) == IF S = {} THEN v ELSE CHOOSE e \in Orders : e[1] = e[2] /\ e[1] \in S

DistinctSenders(S) == {m[1].sender : m \in S}

TypeOK ==
  /\ loc \in [0 .. N - 1 -> {"phase1", "wait1", "phase2", "wait2", "done", "crashed", "choosing"}]
  /\ inbox \in [0 .. N - 1 -> [0 .. N - 1 -> Values \cup {Bottom}]]
  /\ prop \in [0 .. N - 1 -> Values]
  /\ estimate \in [0 .. N - 1 -> Values \cup {Bottom}]
  /\ decided \in [0 .. N - 1 -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Msgs
  /\ recv \in [0 .. N - 1 -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 0 .. N - 1 |-> "phase1"]
  /\ inbox = [p \in 0 .. N - 1 |-> [q \in 0 .. N - 1 |-> Bottom]]
  /\ prop \in [0 .. N - 1 -> Values]
  /\ estimate = [p \in 0 .. N - 1 |-> Bottom]
  /\ decided = [p \in 0 .. N - 1 |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 0 .. N - 1 |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "phase1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p] \X Orders}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<inbox, prop, estimate, decided, crashed, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "phase2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p] \X Orders}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<inbox, prop, estimate, decided, crashed, recv>>

\* A pending message of the wrong type is left untouched for a future phase.
Receive(p, m) ==
  /\ m \in sent
  /\ m \notin recv[p]
  /\ m[1].type = loc[p]
  /\ inbox' = [inbox EXCEPT ![p][m[1].sender] = m[1].val]
  /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

\* The estimate is the reduction (max, in the paper's total order) of the view.
ComputeAndPrepare(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(DistinctSenders(recv[p]) \cap (0 .. N - 1)) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = Bump(Bottom, {inbox[p][q] : q \in 0 .. N - 1})]
  /\ loc' = [loc EXCEPT ![p] = "phase2"]
  /\ UNCHANGED <<inbox, prop, decided, crashed, sent, recv>>

DecideAndFinish(p, v) ==
  /\ loc[p] = "wait2"
  /\ {m \in recv[p] : m[1].type = "phase2" /\ m[2] = v} >= N - T
  /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<inbox, prop, estimate, crashed, sent, recv>>

Choose(p) ==
  /\ loc[p] = "wait2"
  /\ {m \in recv[p] : m[1].type = "phase2"} = sent \cap ([type |-> "phase2", val |-> prop[p], sender |-> p] \X Orders)
  /\ Cardinality(DistinctSenders(recv[p]) \cap (0 .. N - 1)) = N
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<inbox, prop, estimate, decided, crashed, sent, recv>>

DecideFromView(p) ==
  /\ loc[p] = "choosing"
  /\ decided' = [decided EXCEPT ![p] = inbox[p][CHOOSE q \in 0 .. N - 1 : inbox[p][q] # Bottom]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<inbox, prop, estimate, crashed, sent, recv>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<inbox, prop, estimate, decided, sent, recv>>

Next ==
  \/ \E p \in 0 .. N - 1 : BroadcastPhase1(p) \/ BroadcastPhase2(p) \/ ComputeAndPrepare(p) \/ Choose(p) \/ DecideFromView(p) \/ Crash(p)
  \/ \E p \in 0 .. N - 1, m \in Msgs : Receive(p, m)
  \/ \E p \in 0 .. N - 1, v \in Orders : DecideAndFinish(p, v)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 0 .. N - 1 : WF_vars(\E m \in Msgs : Receive(p, m))
  /\ \A p \in 0 .. N - 1 : WF_vars(DecideFromView(p))
  /\ \A p \in 0 .. N - 1 : WF_vars(Choose(p))
  /\ \A p \in 0 .. N - 1 : WF_vars(DecideAndFinish(p, CHOOSE v \in Orders : TRUE))

Validity == \A p \in 0 .. N - 1 : decided[p] # Bottom => \E q \in 0 .. N - 1 : prop[q] = decided[p]

Agreement == \A p, q \in 0 .. N - 1 : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in 0 .. N - 1 : loc[p] \in {"crashed", "done"})

\* C1 is the condition on which the two-phase-commit decision is safe.
MaxValue == CHOOSE x \in Values : \A y \in Values : y <= x
AtLeastFPlus1Max == Cardinality({p \in 0 .. N - 1 : prop[p] = MaxValue}) >= F + 1
ConditionalTermination == AtLeastFPlus1Max ~> Termination

Properties == Termination /\ ConditionalTermination
====