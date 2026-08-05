---- MODULE cbc_max ----
EXTENDS Naturals

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ F \in Nat /\ T > F /\ 2 * T < N /\ Bottom \notin Values

VARIABLES pc, localView, proposal, estimate, decided, crashCount, sent, received

vars == <<pc, localView, proposal, estimate, decided, crashCount, sent, received>>

Phases == {"bcast1", "wait1", "prep", "bcast2", "wait2", "done", "crashed", "choose"}
Types == {"phase1", "phase2"}
Msgs == [type : Types, val : Values, snd : 0..(N - 1), e : Values]

MaxOf(S) == CHOOSE e \in S : \A f \in S : f <= e

Init ==
    /\ pc = [p \in 0..(N - 1) |-> "bcast1"]
    /\ localView = [p \in 0..(N - 1), q \in 0..(N - 1) |-> Bottom]
    /\ proposal \in [p \in 0..(N - 1) |-> Values]
    /\ estimate = [p \in 0..(N - 1) |-> Bottom]
    /\ decided = [p \in 0..(N - 1) |-> Bottom]
    /\ crashCount = 0
    /\ sent = {}
    /\ received = [p \in 0..(N - 1) |-> {}]

SendPhase1(p) ==
    /\ pc[p] = "bcast1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[p], snd |-> p, e |-> Bottom]}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<localView, proposal, estimate, decided, crashCount, received>>

SendPhase2(p) ==
    /\ pc[p] = "prep"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[p], snd |-> p, e |-> estimate[p]]}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<localView, proposal, estimate, decided, crashCount, received>>

ReceivePhase1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ localView[p][m.snd] = Bottom
    /\ localView' = [localView EXCEPT ![p][m.snd] = m.val]
    /\ received' = [received EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<pc, proposal, estimate, decided, crashCount, sent>>

ReceivePhase2(p, m) ==
    /\ pc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ localView[p][m.snd] = Bottom
    /\ localView' = [localView EXCEPT ![p][m.snd] = m.val]
    /\ received' = [received EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<pc, proposal, estimate, decided, crashCount, sent>>

Prep(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({m \in received[p] : m.type = "phase1"}) >= N - T
    /\ \E q \in 0..(N - 1) : localView[p][q] # Bottom
    /\ estimate' = [estimate EXCEPT ![p] = MaxOf({localView[p][q] : q \in 0..(N - 1)} \cup {Bottom})]
    /\ pc' = [pc EXCEPT ![p] = "prep"]
    /\ UNCHANGED <<localView, proposal, decided, crashCount, sent, received>>

Decide(p) ==
    /\ pc[p] = "wait2"
    /\ \E e \in Values :
        /\ Cardinality({m \in received[p] : m.type = "phase2" /\ m.e = e}) >= N - T
        /\ decided' = [decided EXCEPT ![p] = e]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<localView, proposal, estimate, crashCount, sent, received>>

Choose(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({m \in received[p] : m.type = "phase2"}) = N
    /\ \E e \in Values : \E q \in 0..(N - 1) :
        /\ localView[p][q] # Bottom
        /\ e = localView[p][q]
        /\ decided' = [decided EXCEPT ![p] = e]
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<localView, proposal, estimate, crashCount, sent, received>>

Crash(p) ==
    /\ pc[p] \notin {"crashed", "done"}
    /\ crashCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED <<localView, proposal, estimate, decided, sent, received>>

Next ==
    \/ \E p \in 0..(N - 1) : SendPhase1(p) \/ SendPhase2(p) \/ Prep(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
    \/ \E p \in 0..(N - 1), m \in Msgs : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

TypeOK ==
    /\ pc \in [0..(N - 1) -> Phases]
    /\ localView \in [0..(N - 1), 0..(N - 1) -> Values \cup {Bottom}]
    /\ proposal \in [0..(N - 1) -> Values]
    /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ crashCount \in 0..F
    /\ sent \subseteq Msgs
    /\ received \in [0..(N - 1) -> SUBSET Msgs]

Validity == \A p \in 0..(N - 1) : decided[p] # Bottom => decided[p] \in Values

Agreement == \A p, q \in 0..(N - 1) :
    (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Finish == \A p \in 0..(N - 1) : pc[p] \in {"crashed", "done"}

ConditionC1 == (N - T) * Cardinality(Values) < (N - T) ^ 2

Termination == (Finish /\ ConditionC1) ~> Finish

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendPhase1(0))
    /\ WF_vars(SendPhase2(0))
    /\ WF_vars(Prep(0))
    /\ WF_vars(Decide(0))
    /\ WF_vars(Choose(0))

====