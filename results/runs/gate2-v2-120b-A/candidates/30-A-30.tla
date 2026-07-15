---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS N, T, F, Values, Bottom

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
Proc == 1 .. N
Phase == {"bc1", "wait1", "prep", "bc2", "wait2", "choosing", "done", "crashed"}
MsgType == {"phase1", "phase2"}
Msg == [type : MsgType, sender : Proc, prop : Values, est : Values \cup {Bottom}]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    pc,          \* control location of each process:  map Proc -> Phase
    propVal,     \* proposed value of each process:    map Proc -> Values
    view,        \* local view matrix:                 map Proc -> [Proc -> Values \cup {Bottom}]
    est,         \* estimated value after phase1:      map Proc -> Values \cup {Bottom}
    dec,         \* decision value:                    map Proc -> Values \cup {Bottom}
    crashedCnt,  \* number of crashed processes:       Nat
    sent,        \* set of sent messages:              SUBSET Msg
    recv         \* received messages per process:     map Proc -> SUBSET Msg

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ pc = [p \in Proc |-> "bc1"]
    /\ propVal \in [Proc -> Values]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCnt = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
MaxInView(p) ==
    LET vals == { v \in view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
    IF vals = {} THEN Bottom ELSE Max(vals)

CountDistinctSenders(msgs, typ) ==
    Cardinality({ m.sender : m \in msgs /\ m.type = typ })

ReceivedFrom(p, typ) ==
    { m.sender : m \in recv[p] /\ m.type = typ }

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

BroadcastPhase1(p) ==
    /\ pc[p] = "bc1"
    /\ sent' = sent \cup { [type |-> "phase1",
                           sender |-> p,
                           prop |-> propVal[p],
                           est |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<propVal, view, est, dec, crashedCnt, recv>>

ReceivePhase1(p) ==
    /\ pc[p] = "wait1"
    /\ \E m \in sent :
         /\ m.type = "phase1"
         /\ m.sender # p
         /\ view[p][m.sender] = Bottom
    /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, propVal, est, dec, crashedCnt, sent>>

Phase1ToPhase2(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality(ReceivedFrom(p, "phase1")) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInView(p)]
    /\ pc' = [pc EXCEPT ![p] = "bc2"]
    /\ UNCHANGED <<propVal, view, dec, crashedCnt, sent, recv>>

BroadcastPhase2(p) ==
    /\ pc[p] = "bc2"
    /\ sent' = sent \cup { [type |-> "phase2",
                           sender |-> p,
                           prop |-> propVal[p],
                           est |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<propVal, view, est, dec, crashedCnt, recv>>

ReceivePhase2(p) ==
    /\ pc[p] = "wait2"
    /\ \E m \in sent :
         /\ m.type = "phase2"
         /\ m.sender # p
    /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, propVal, est, dec, crashedCnt, sent>>

DecideFromEstimates(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
         /\ Cardinality({ m : m \in recv[p] /\ m.type = "phase2" /\ m.est = v }) >= N - T
    /\ LET v == CHOOSE w \in Values :
               Cardinality({ m : m \in recv[p] /\ m.type = "phase2" /\ m.est = w }) >= N - T IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVal, view, est, crashedCnt, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({ m : m \in recv[p] /\ m.type = "phase2" }) = N
    /\ \A v \in Values :
         Cardinality({ m : m \in recv[p] /\ m.type = "phase2" /\ m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<propVal, view, est, dec, crashedCnt, sent, recv>>

ChooseAndDecide(p) ==
    /\ pc[p] = "choosing"
    /\ \E v \in Values :
         /\ (\E q \in Proc : view[p][q] = v)
    /\ LET v == CHOOSE w \in Values :
               \E q \in Proc : view[p][q] = w IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVal, view, est, crashedCnt, sent, recv>>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCnt < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCnt' = crashedCnt + 1
    /\ UNCHANGED <<propVal, view, est, dec, sent, recv>>

SelfLoop ==
    UNCHANGED <<pc, propVal, view, est, dec, crashedCnt, sent, recv>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc : ReceivePhase1(p)
    \/ \E p \in Proc : Phase1ToPhase2(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc : ReceivePhase2(p)
    \/ \E p \in Proc : DecideFromEstimates(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)
    \/ SelfLoop

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, propVal, view, est, dec, crashedCnt, sent, recv>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> Phase]
    /\ propVal \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCnt \in Nat
    /\ crashedCnt <= F
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]
    /\ \A p \in Proc : \A m \in recv[p] :
         /\ m.sender \in Proc
         /\ m.type \in MsgType
         /\ m.prop \in Values
         /\ (m.type = "phase1" => m.est = Bottom)
         /\ (m.type = "phase2" => m.est \in Values \cup {Bottom})

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => \E q \in Proc : propVal[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

(*--------------------------------------------------------------------
  Weak fairness assumptions (for liveness, not part of invariants)
--------------------------------------------------------------------*)
\* These are expressed in the .cfg file via WF or SF, not here.

====