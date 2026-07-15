---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (as required by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    N,            \* number of processes
    T,            \* maximum number of tolerated faults
    F,            \* actual number of faults allowed to crash
    Values,       \* finite totally‑ordered set of proposal values
    Bottom        \* special value distinct from all elements of Values

(*-----------------------------------------------------------------
  Types (for readability)
-----------------------------------------------------------------*)
Proc == 1..N
MsgType == {"p1", "p2"}

Message == [type : MsgType,
            prop : Values,
            est  : Values \cup {Bottom},
            sender : Proc]

StateLoc == {"bcast1", "wait1", "bcast2", "wait2",
             "done", "crashed", "choosing"}

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    loc,          \* [Proc -> StateLoc]  current control location
    propVals,    \* [Proc -> Values]     each process's initial proposal
    view,        \* [Proc -> [Proc -> Values \cup {Bottom}]]
    est,         \* [Proc -> Values \cup {Bottom}] estimated value
    dec,         \* [Proc -> Values \cup {Bottom}] decision value
    crashedCount,\* Nat   number of processes that have crashed
    sent,        \* SUBSET Message   all messages that have been broadcast
    rcv          \* [Proc -> SUBSET Message]  messages received per process

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Max(vs) == IF vs = {} THEN Bottom ELSE
               CHOOSE x \in vs : \A y \in vs : y <= x

CountReceived(p, t) ==
    Cardinality({ m \in rcv[p] : m.type = t })

Phase1Send(p) ==
    [type |-> "p1",
     prop |-> propVals[p],
     est  |-> Bottom,
     sender |-> p]

Phase2Send(p) ==
    [type |-> "p2",
     prop |-> propVals[p],
     est  |-> est[p],
     sender |-> p]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ loc = [p \in Proc |-> "bcast1"]
    /\ propVals \in [Proc -> Values]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ rcv = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
BroadcastPhase1(p) ==
    /\ loc[p] = "bcast1"
    /\ LET m == Phase1Send(p) IN
        /\ sent' = sent \cup {m}
        /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<propVals, view, est, dec, crashedCount>>

ReceivePhase1(p) ==
    /\ loc[p] \in {"wait1", "wait2", "choosing", "bcast2"}
    /\ \E m \in sent :
          /\ m.type = "p1"
          /\ m.sender \notin view[p]
          /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
          /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ UNCHANGED <<loc, propVals, est, dec, crashedCount, sent>>

ComputeEst(p) ==
    /\ loc[p] = "wait1"
    /\ CountReceived(p, "p1") >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ loc' = [loc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<propVals, view, dec, crashedCount, sent, rcv>>

BroadcastPhase2(p) ==
    /\ loc[p] = "bcast2"
    /\ LET m == Phase2Send(p) IN
        /\ sent' = sent \cup {m}
        /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<propVals, view, est, dec, crashedCount>>

ReceivePhase2(p) ==
    /\ loc[p] \in {"wait2", "choosing"}
    /\ \E m \in sent :
          /\ m.type = "p2"
          /\ m.sender \notin view[p]
          /\ view' = [view EXCEPT ![p][m.sender] = m.est]
          /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ UNCHANGED <<loc, propVals, est, dec, crashedCount, sent>>

DecideFromPhase2(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
          /\ Cardinality({ m \in rcv[p] : m.type = "p2" /\ m.est = v }) >= N - T
    /\ LET v == CHOOSE w \in Values :
           Cardinality({ m \in rcv[p] : m.type = "p2" /\ m.est = w }) >= N - T IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVals, view, est, crashedCount, sent, rcv>>

MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ \A v \in Values :
          Cardinality({ m \in rcv[p] : m.type = "p2" /\ m.est = v }) < N - T
    /\ Cardinality({ m \in rcv[p] : m.type = "p2" }) = N
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<propVals, view, est, dec, crashedCount, sent, rcv>>

ChooseAndDecide(p) ==
    /\ loc[p] = "choosing"
    /\ \E v \in Values :
          v \in { view[p][q] : q \in Proc }
    /\ LET v == CHOOSE w \in Values :
           w \in { view[p][q] : q \in Proc } IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVals, view, est, crashedCount, sent, rcv>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashedCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<propVals, view, est, dec, sent, rcv>>

Next ==
    \E p \in Proc :
        \/ BroadcastPhase1(p)
        \/ ReceivePhase1(p)
        \/ ComputeEst(p)
        \/ BroadcastPhase2(p)
        \/ ReceivePhase2(p)
        \/ DecideFromPhase2(p)
        \/ MoveToChoosing(p)
        \/ ChooseAndDecide(p)
        \/ Crash(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<loc, propVals, view, est, dec,
                 crashedCount, sent, rcv>>

(*-----------------------------------------------------------------
  Type correctness invariant (not required in the config but useful)
-----------------------------------------------------------------*)
TypeOK ==
    /\ loc \in [Proc -> StateLoc]
    /\ propVals \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ dec \in [Proc -> Values \cup {Bottom}]
    /\ crashedCount \in Nat
    /\ crashedCount <= N
    /\ sent \subseteq Message
    /\ rcv \in [Proc -> SUBSET Message]

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
Validity ==
    \A p \in Proc :
        /\ dec[p] # Bottom
        => dec[p] \in Values
        /\ \E q \in Proc : propVals[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

=============================================================================