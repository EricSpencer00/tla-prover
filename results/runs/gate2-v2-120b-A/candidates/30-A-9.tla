---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* -----------------------------
\* Constants (to be set in the .cfg)
\* -----------------------------
CONSTANTS N, T, F, Values, Bottom

\* -----------------------------
\* Derived sets
\* -----------------------------
Proc == 1..N
Phase == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choose"}
MsgType == {"phase1", "phase2"}

\* Message definition
Msg == [type : MsgType,
        sender : Proc,
        value : Values \cup {Bottom},
        est   : Values \cup {Bottom}] \* `est` is Bottom for phase1

\* -----------------------------
\* Variables
\* -----------------------------
VARIABLES
    pc,          \* control location per process
    localView,  \* [proc -> [proc -> Values \cup {Bottom}]]
    prop,       \* proposed value per process
    est,        \* estimated value per process
    dec,        \* decision value per process
    crashedCnt, \* number of crashed processes
    Sent,       \* set of messages that have been sent
    recv        \* [proc -> SUBSET Msg] messages received by each process

\* -----------------------------
\* Helper definitions
\* -----------------------------
Max(vset) == 
    IF vset = {} THEN Bottom 
    ELSE CHOOSE x \in vset : \A y \in vset : y <= x

Cnt(mset) == Cardinality(mset)

\* -----------------------------
\* Initial state
\* -----------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ prop \in [p \in Proc |-> Values]
    /\ localView = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCnt = 0
    /\ Sent = {}
    /\ recv = [p \in Proc |-> {}]

\* -----------------------------
\* Actions
\* -----------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ Sent' = Sent \cup { [type |-> "phase1",
                           sender |-> p,
                           value |-> prop[p],
                           est |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED <<localView, prop, est, dec, crashedCnt, recv>>

ReceivePhase1(p) ==
    /\ pc[p] = "w1"
    /\ \E m \in Sent :
          /\ m.type = "phase1"
          /\ m.sender \notin recv[p]
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.value]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashedCnt, Sent>>

Prepare(p) ==
    /\ pc[p] = "w1"
    /\ \A q \in Proc : \E s \in Sent : 
          /\ s.type = "phase1"
          /\ s.sender = q
    /\ est' = [est EXCEPT ![p] = Max({localView[p][q] : q \in Proc})]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED <<prop, localView, dec, crashedCnt, Sent, recv>>

BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ Sent' = Sent \cup { [type |-> "phase2",
                           sender |-> p,
                           value |-> prop[p],
                           est |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED <<localView, prop, est, dec, crashedCnt, recv>>

ReceivePhase2(p) ==
    /\ pc[p] = "w2"
    /\ \E m \in Sent :
          /\ m.type = "phase2"
          /\ m.sender \notin recv[p]
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.est]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashedCnt, Sent>>

Decide(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Values :
          /\ Cnt({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<localView, prop, est, crashedCnt, Sent, recv>>

Choose(p) ==
    /\ pc[p] = "w2"
    /\ \A v \in Values :
          Cnt({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) < N - T
    /\ \E v \in Values :
          /\ v \in { localView[p][q] : q \in Proc }
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<localView, prop, est, crashedCnt, Sent, recv>>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCnt < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCnt' = crashedCnt + 1
    /\ UNCHANGED <<localView, prop, est, dec, Sent, recv>>

\* -----------------------------
\* Next-state relation
\* -----------------------------
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc : ReceivePhase1(p)
    \/ \E p \in Proc : Prepare(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc : ReceivePhase2(p)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* -----------------------------
\* Specification
\* -----------------------------
Spec == Init /\ [][Next]_<<pc, prop, localView, est, dec, crashedCnt, Sent, recv>>

\* -----------------------------
\* Type correctness invariant
\* -----------------------------
TypeOK ==
    /\ pc \in [Proc -> Phase]
    /\ prop \in [Proc -> Values]
    /\ localView \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCnt \in Nat
    /\ crashedCnt <= F
    /\ Sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* -----------------------------
\* Safety properties
\* -----------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* -----------------------------
\* (Optional) Liveness property can be added in the .cfg
\* -----------------------------

====