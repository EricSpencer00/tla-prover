---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    N,          \* number of processes
    T,          \* tolerated faults (2*T < N)
    F,          \* actual crash faults (0 <= F <= T)
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special bottom value, not in Values

\* -----------------------------------------------------------------
\* Basic sets
\* -----------------------------------------------------------------
Proc == 1..N
Value == Values \cup {Bottom}
MsgType == {"phase1", "phase2"}

\* -----------------------------------------------------------------
\* Message definition
\* -----------------------------------------------------------------
Message == 
    [type : MsgType,
     sender : Proc,
     value : Value,
     est : Value]   \* for phase‑2 messages, est = estimated value; otherwise Bottom

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES 
    loc,        \* control location of each process
    view,       \* N×N matrix of received values (view[p][q] = value from q as seen by p)
    prop,       \* proposed value of each process
    est,        \* estimated value after phase 1
    dec,        \* decision value (Bottom until decided)
    crashedCnt, \* number of crashed processes
    msgs,       \* set of all sent messages
    recv        \* messages received by each process

\* -----------------------------------------------------------------
\* Enumerated locations
\* -----------------------------------------------------------------
Locs == {"broadcast1", "wait1", "broadcast2", "wait2", 
         "choosing", "done", "crashed"}

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
\* Set of senders from which p has already received a phase‑1 message
Senders1(p) == { m.sender : m \in recv[p] /\ m.type = "phase1" }

\* Set of senders from which p has already received a phase‑2 message
Senders2(p) == { m.sender : m \in recv[p] /\ m.type = "phase2" }

\* Set of estimated values seen in phase‑2 messages received by p
EstVals2(p) == { m.est : m \in recv[p] /\ m.type = "phase2" }

\* Maximum value among a set S ⊆ Values (Bottom if S = {}).
\* Values are assumed totally ordered (e.g., natural numbers).
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in Values :
            (\A w \in S : w <= v) /\ 
            (\A u \in Values :
                (\A w \in S : w <= u) => v <= u)

\* Maximum of the values stored in p's view (ignoring Bottom)
MaxInView(p) ==
    MaxVal({ view[p][q] : q \in Proc })

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ loc = [p \in Proc |-> "broadcast1"]
    /\ prop \in [p \in Proc |-> Values]               \* each process proposes some value
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCnt = 0
    /\ msgs = {}
    /\ recv = [p \in Proc |-> {}]

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ UNCHANGED <<view, est, dec, crashedCnt, recv>>
    /\ msgs' = msgs \cup {
            [type |-> "phase1",
             sender |-> p,
             value |-> prop[p],
             est |-> Bottom]
        }
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<prop>>

Receive1(p, m) ==
    /\ loc[p] = "wait1"
    /\ m \in msgs
    /\ m.type = "phase1"
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ UNCHANGED <<loc, prop, est, dec, crashedCnt, msgs>>

ComputeEst(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality(Senders1(p)) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInView(p)]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, prop, dec, crashedCnt, msgs, recv>>

Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ UNCHANGED <<view, recv, dec, crashedCnt>>
    /\ msgs' = msgs \cup {
            [type |-> "phase2",
             sender |-> p,
             value |-> prop[p],
             est |-> est[p]]
        }
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<prop, est>>

Receive2(p, m) ==
    /\ loc[p] = "wait2"
    /\ m \in msgs
    /\ m.type = "phase2"
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ UNCHANGED <<loc, prop, est, dec, crashedCnt, msgs>>

Decide(p, v) ==
    /\ loc[p] = "wait2"
    /\ v \in Values
    /\ Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCnt, msgs, recv>>

MoveChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality(Senders2(p)) = N
    /\ \A v \in Values :
          Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, crashedCnt, msgs, recv>>

Choose(p, v) ==
    /\ loc[p] = "choosing"
    /\ v \in Values
    /\ v \in { view[p][q] : q \in Proc }   \* value appears in p's local view
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCnt, msgs, recv>>

Crash(p) ==
    /\ crashedCnt < F
    /\ loc[p] # "crashed"
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCnt' = crashedCnt + 1
    /\ UNCHANGED <<view, prop, est, dec, msgs, recv>>

\* -----------------------------------------------------------------
\* Next-state relation (any enabled action for any process)
\* -----------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Broadcast1(p)
    \/ \E p \in Proc, m \in msgs : Receive1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : Broadcast2(p)
    \/ \E p \in Proc, m \in msgs : Receive2(p, m)
    \/ \E p \in Proc, v \in Values : Decide(p, v)
    \/ \E p \in Proc : MoveChoosing(p)
    \/ \E p \in Proc, v \in Values : Choose(p, v)
    \/ \E p \in Proc : Crash(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, view, prop, est, dec, crashedCnt, msgs, recv>>

\* -----------------------------------------------------------------
\* Type correctness invariant
\* -----------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> Value]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Value]
    /\ dec \in [Proc -> Value]
    /\ crashedCnt \in Nat
    /\ msgs \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* -----------------------------------------------------------------
\* Safety properties
\* -----------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom =>
            /\ dec[p] \in Values
            /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

====