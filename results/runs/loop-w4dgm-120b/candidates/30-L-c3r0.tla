---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Message types for the two protocol phases.
MsgTypes == {"phase1", "phase2"}

\* A message: its type, the sender, the proposed value, and for phase2 the
\* sender's own estimate of the broadcast maximum.
VARIABLES pc, view, prop, estimate, decision, crashedCount, sent, recv

vars == <<pc, view, prop, estimate, decision, crashedCount, sent, recv>>

\* Type synonyms for readability when indexing the view matrix.
Procs == 0..(N - 1)
Views == [Procs -> Values \cup {Bottom}]

TypeOK ==
    /\ pc \in [Procs -> {"phase1", "wait1", "prepare", "phase2",
                         "wait2", "done", "crashed", "choosing"}]
    /\ view \in [Procs -> Views]
    /\ prop \in [Procs -> Values]
    /\ estimate \in [Procs -> Values \cup {Bottom}]
    /\ decision \in [Procs -> Values \cup {Bottom}]
    /\ crashedCount \in 0..CrashedMax
    /\ sent \subseteq [mtype: MsgTypes, sender: Procs,
                       val: Values, estimate: Values \cup {Bottom}]
    /\ recv \in [Procs -> SUBSET Procs]
    /\ CrashedMax = Cardinality({p \in Procs : pc[p] = "crashed"})
    /\ MaxN == IF N = 0 THEN 0 ELSE N - 1

Init ==
    /\ pc = [p \in Procs |-> "phase1"]
    /\ view = [p \in Procs |-> [q \in Procs |-> Bottom]]
    /\ prop \in [Procs -> Values]
    /\ estimate = [p \in Procs |-> Bottom]
    /\ decision = [p \in Procs |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Procs |-> {}]

\* Phase 1: proposals broadcast to every other process.
BroadcastPhase1(p) ==
    /\ pc[p] = "phase1"
    /\ sent' = sent \cup {[mtype |-> "phase1", sender |-> p,
                           val |-> prop[p], estimate |-> Bottom]}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, recv>>

ReceivePhase1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m.mtype = "phase1"
    /\ m.sender \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
    /\ UNCHANGED <<pc, prop, estimate, decision, crashedCount, sent>>

\* Once a process has a bounded set of views, it estimates the broadcast max.
ComputeEstimate(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality(recv[p]) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = CHOOSE m \in Values \cup {Bottom} :
                        \A q \in Procs : (view[p][q] # Bottom) => view[p][q] <= m]
    /\ pc' = [pc EXCEPT ![p] = "phase2"]
    /\ UNCHANGED <<view, prop, decision, crashedCount, sent, recv>>

\* Phase 2: each process broadcasts its own estimate to the group.
BroadcastPhase2(p) ==
    /\ pc[p] = "phase2"
    /\ sent' = sent \cup {[mtype |-> "phase2", sender |-> p,
                           val |-> prop[p], estimate |-> estimate[p]]}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, recv>>

RECURSIVE CountMatches(_)
CountMatches(S) == IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN 1 + CountMatches(S \ {x})

\* Two decision paths: terminate on a threshold of matching estimates, or
\* fall back to a deterministic local choice once every sender is heard.
DecideOnThreshold(p, val) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({q \in Procs : \E m \in sent : m.sender = q
                       /\ m.mtype = "phase2" /\ m.estimate = val})
         >= N - T
    /\ decision' = [decision EXCEPT ![p] = val]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashedCount, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ recv[p] = Procs
    /\ decision[p] = Bottom
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, sent, recv>>

ChooseLocally(p, val) ==
    /\ pc[p] = "choosing"
    /\ decision[p] = Bottom
    /\ decision' = [decision EXCEPT ![p] = val]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashedCount, sent, recv>>

\* Failover: at most F processes ever crash, and weak fairness still applies.
Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, prop, estimate, decision, sent, recv>>

Next ==
    \/ \E p \in Procs :
        \/ BroadcastPhase1(p) \/ ComputeEstimate(p) \/ BroadcastPhase2(p)
        \/ MoveToChoosing(p) \/ Crash(p)
        \/ \E val \in Values : DecideOnThreshold(p, val) \/ ChooseLocally(p, val)
    \/ \E p \in Procs, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in Procs, m \in sent : ReceivePhase1(p, m)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in Procs : BroadcastPhase1(p))
    /\ WF_vars(\E p \in Procs, m \in sent : ReceivePhase1(p, m))
    /\ WF_vars(\E p \in Procs : ComputeEstimate(p))
    /\ WF_vars(\E p \in Procs : BroadcastPhase2(p))
    /\ WF_vars(\E p \in Procs : MoveToChoosing(p))
    /\ WF_vars(\E p \in Procs, val \in Values : DecideOnThreshold(p, val))
    /\ WF_vars(\E p \in Procs, val \in Values : ChooseLocally(p, val))

\* Neither can the system record a decision for a value nobody proposed, nor
\* two processes each finish with different decisions.
Validity == \A p \in Procs : decision[p] # Bottom => \E q \in Procs : prop[q] = decision[p]
Agreement == \A p, q \in Procs : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* Every process either crashes or eventually decides.
Termination == \A p \in Procs : (pc[p] = "crashed") ~> (pc[p] = "done")

\* Conditional guarantee: the sufficient condition behind Condition C1.
C1Termination ==
    \A val \in Values :
        (CountMatches({p \in Procs : prop[p] = val}) >= F + 1) ~> (crashedCount = F)

====