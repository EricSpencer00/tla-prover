---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS N, T, F, Values, Bottom

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
ValueSet == Values \cup {Bottom}
ProcSet  == 1..N

MsgType  == {"phase1", "phase2"}

Message == [type : MsgType,
            val  : ValueSet,
            sender : ProcSet,
            est  : ValueSet \cup {Bottom}]  \* est is Bottom for phase1 msgs

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    control,      \* [p \in ProcSet -> {"broadcast1", "wait1", "broadcast2", "wait2", "decided", "crashed", "choosing"}]
    view,         \* [p \in ProcSet -> [q \in ProcSet -> ValueSet]]
    prop,         \* [p \in ProcSet -> ValueSet]            \* proposed value
    est,          \* [p \in ProcSet -> ValueSet]            \* estimated after phase1
    decision,    \* [p \in ProcSet -> ValueSet]            \* Bottom means not decided
    crashedCount, \* Nat
    sent,          \* SUBSET Message
    recv           \* [p \in ProcSet -> SUBSET Message]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
OtherProcs(p) == ProcSet \ {p}

MaxInView(p) ==
    LET vals == { view[p][q] : q \in ProcSet } IN
    IF vals = {} THEN Bottom
    ELSE CHOOSE v \in vals : \A w \in vals : v >= w

MessagesFrom(p, mtype) ==
    { m \in recv[p] : m.type = mtype }

MessagesFromTo(p, senderSet, mtype) ==
    { m \in recv[p] : m.type = mtype /\ m.sender \in senderSet }

SameEstCount(p, v) ==
    Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v })

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ control = [p \in ProcSet |-> "broadcast1"]
    /\ view    = [p \in ProcSet |-> [q \in ProcSet |-> Bottom]]
    /\ prop    = [p \in ProcSet |-> CHOOSE v \in Values : TRUE] \* any value from Values
    /\ est     = [p \in ProcSet |-> Bottom]
    /\ decision= [p \in ProcSet |-> Bottom]
    /\ crashedCount = 0
    /\ sent    = {}
    /\ recv    = [p \in ProcSet |-> {}]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
BroadcastPhase1(p) ==
    /\ control[p] = "broadcast1"
    /\ sent' = sent \cup { [type |-> "phase1",
                           val  |-> prop[p],
                           sender |-> p,
                           est  |-> Bottom] }
    /\ control' = [control EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << view, prop, est, decision, crashedCount, recv >>

ReceivePhase1(p) ==
    \E m \in sent :
        /\ m.type = "phase1"
        /\ m.sender \in ProcSet
        /\ m.val \in Values
        /\ m NOT IN recv[p]
        /\ view' = [view EXCEPT ![p][m.sender] = m.val]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << control, prop, est, decision, crashedCount, sent >>

Phase1ToPhase2(p) ==
    /\ control[p] = "wait1"
    /\ Cardinality({ m \in recv[p] : m.type = "phase1" }) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInView(p)]
    /\ control' = [control EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED << view, prop, decision, crashedCount, sent, recv >>

BroadcastPhase2(p) ==
    /\ control[p] = "broadcast2"
    /\ sent' = sent \cup { [type |-> "phase2",
                           val  |-> prop[p],
                           sender |-> p,
                           est  |-> est[p]] }
    /\ control' = [control EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << view, prop, est, decision, crashedCount, recv >>

ReceivePhase2(p) ==
    \E m \in sent :
        /\ m.type = "phase2"
        /\ m.sender \in ProcSet
        /\ m.val \in Values
        /\ m.est \in ValueSet
        /\ m NOT IN recv[p]
        /\ view' = [view EXCEPT ![p][m.sender] = m.val]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << control, prop, est, decision, crashedCount, sent >>

DecideFromPhase2(p) ==
    /\ control[p] = "wait2"
    /\ \E v \in Values :
        /\ SameEstCount(p, v) >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ control' = [control EXCEPT ![p] = "decided"]
        /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
    /\ control[p] = "wait2"
    /\ Cardinality({ m \in recv[p] : m.type = "phase2" }) = N
    /\ \A v \in Values : SameEstCount(p, v) < N - T
    /\ control' = [control EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << view, prop, est, decision, crashedCount, sent, recv >>

ChooseAndDecide(p) ==
    /\ control[p] = "choosing"
    /\ \E v \in Values :
        /\ v \in { view[p][q] : q \in ProcSet }
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ control' = [control EXCEPT ![p] = "decided"]
        /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
    /\ crashedCount < F
    /\ crashedCount' = crashedCount + 1
    /\ control' = [control EXCEPT ![p] = "crashed"]
    /\ UNCHANGED << view, prop, est, decision, sent, recv >>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in ProcSet : BroadcastPhase1(p)
    \/ \E p \in ProcSet : ReceivePhase1(p)
    \/ \E p \in ProcSet : Phase1ToPhase2(p)
    \/ \E p \in ProcSet : BroadcastPhase2(p)
    \/ \E p \in ProcSet : ReceivePhase2(p)
    \/ \E p \in ProcSet : DecideFromPhase2(p)
    \/ \E p \in ProcSet : MoveToChoosing(p)
    \/ \E p \in ProcSet : ChooseAndDecide(p)
    \/ \E p \in ProcSet : Crash(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<control, view, prop, est, decision, crashedCount, sent, recv>>

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ control \in [ProcSet -> {"broadcast1","wait1","broadcast2","wait2","decided","crashed","choosing"}]
    /\ view    \in [ProcSet -> [ProcSet -> ValueSet]]
    /\ prop    \in [ProcSet -> Values]
    /\ est     \in [ProcSet -> ValueSet]
    /\ decision\in [ProcSet -> ValueSet]
    /\ crashedCount \in Nat
    /\ sent    \subseteq Message
    /\ recv    \in [ProcSet -> SUBSET Message]

(*-----------------------------------------------------------------
  Safety property: Validity
-----------------------------------------------------------------*)
Validity ==
    \A p \in ProcSet :
        decision[p] # Bottom => decision[p] \in Values

(*-----------------------------------------------------------------
  Safety property: Agreement
-----------------------------------------------------------------*)
Agreement ==
    \A p, q \in ProcSet :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

(*-----------------------------------------------------------------
  Optional: the .cfg may refer to these invariant names directly
-----------------------------------------------------------------*)
INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement

====