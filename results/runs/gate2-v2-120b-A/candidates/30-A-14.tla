---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    N,               \* number of processes
    T,               \* maximum number of tolerated faults
    F,               \* maximum number of actual crashes
    Values,          \* finite set of proposal values (totally ordered)
    Bottom           \* special value that is not in Values

(* ------------------------------------------------------------------------ *)
(* Types ------------------------------------------------------------------- *)
Proc == 1..N
MsgType == {"ph1", "ph2"}

Message == [type : MsgType,
            sender : Proc,
            prop : Values \cup {Bottom},
            est   : Values \cup {Bottom}]  \* est is Bottom for ph1

(* ------------------------------------------------------------------------ *)
(* State variables ---------------------------------------------------------- *)

VARIABLES
    loc,            \* control location of each process
    prop,           \* proposed value of each process
    view,           \* N-by-N matrix of received values; view[i][j] is i's view of j's value
    est,            \* estimated value after phase 1
    dec,            \* decision value (Bottom iff undecided)
    crashed,        \* number of crashed processes
    sent,           \* set of all messages that have been sent
    recv            \* mapping proc -> set of messages received by that proc

(* ------------------------------------------------------------------------ *)
(* Helper definitions ------------------------------------------------------ *)

Locs == {"broadcast_ph1", "wait_ph1", "broadcast_ph2", "wait_ph2",
         "choosing", "done", "crashed"}

(* Maximum of a set where Bottom is considered less than any real value *)
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE IF Bottom \in S THEN
        LET Real == S \ {Bottom} IN
            IF Real = {} THEN Bottom ELSE Max(Real)
    ELSE Max(S)

(* ------------------------------------------------------------------------ *)
(* Initialization ---------------------------------------------------------- *)

Init ==
    /\ loc = [i \in Proc |-> "broadcast_ph1"]
    /\ prop \in [i \in Proc |-> Values]
    /\ view = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ est = [i \in Proc |-> Bottom]
    /\ dec = [i \in Proc |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [i \in Proc |-> {}]

(* ------------------------------------------------------------------------ *)
(* Actions ----------------------------------------------------------------- *)

BroadcastPh1(p) ==
    /\ loc[p] = "broadcast_ph1"
    /\ sent' = sent \cup { [type |-> "ph1",
                           sender |-> p,
                           prop |-> prop[p],
                           est |-> Bottom] }
    /\ loc' = [loc EXCEPT ![p] = "wait_ph1"]
    /\ UNCHANGED <<prop, view, est, dec, crashed, recv>>

ReceivePh1(p) ==
    /\ loc[p] = "wait_ph1"
    /\ \E m \in sent :
          /\ m.type = "ph1"
          /\ m.prop \in Values \cup {Bottom}
          /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

Phase1Ready(p) ==
    /\ loc[p] = "wait_ph1"
    /\ Cardinality({ m \in sent : m.type = "ph1" /\ m.sender \in Proc }) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][j] : j \in Proc })]
    /\ loc' = [loc EXCEPT ![p] = "broadcast_ph2"]
    /\ UNCHANGED <<prop, view, dec, crashed, sent, recv>>

BroadcastPh2(p) ==
    /\ loc[p] = "broadcast_ph2"
    /\ sent' = sent \cup { [type |-> "ph2",
                           sender |-> p,
                           prop |-> prop[p],
                           est |-> est[p]] }
    /\ loc' = [loc EXCEPT ![p] = "wait_ph2"]
    /\ UNCHANGED <<prop, view, est, dec, crashed, recv>>

ReceivePh2(p) ==
    /\ loc[p] = "wait_ph2"
    /\ \E m \in sent :
          /\ m.type = "ph2"
          /\ view' = [view EXCEPT ![p][m.sender] = m.est]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

DecideOnEst(p) ==
    /\ loc[p] = "wait_ph2"
    /\ \E v \in Values :
          /\ Cardinality({ m \in recv[p] : m.type = "ph2" /\ m.est = v }) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

AllPh2Received(p) ==
    /\ loc[p] = "wait_ph2"
    /\ Cardinality({ m \in recv[p] : m.type = "ph2" }) = N
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<prop, view, est, dec, crashed, sent, recv>>

Choose(p) ==
    /\ loc[p] = "choosing"
    /\ \E v \in Values :
          /\ v \in { view[p][j] : j \in Proc }
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

Crash(p) ==
    /\ crashed < F
    /\ loc[p] # "crashed"
    /\ crashed' = crashed + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<prop, view, est, dec, sent, recv>>

Next ==
    \/ \E p \in Proc : BroadcastPh1(p)
    \/ \E p \in Proc : ReceivePh1(p)
    \/ \E p \in Proc : Phase1Ready(p)
    \/ \E p \in Proc : BroadcastPh2(p)
    \/ \E p \in Proc : ReceivePh2(p)
    \/ \E p \in Proc : DecideOnEst(p)
    \/ \E p \in Proc : AllPh2Received(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

(* ------------------------------------------------------------------------ *)
(* Specification ----------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<loc, prop, view, est, dec, crashed, sent, recv>>

(* ------------------------------------------------------------------------ *)
(* Invariants -------------------------------------------------------------- *)

(* Type correctness *)
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

(* Validity: any decided value was proposed by some process *)
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => \E q \in Proc : prop[q] = dec[p]

(* Agreement: no two processes decide different values *)
Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

=============================================================================