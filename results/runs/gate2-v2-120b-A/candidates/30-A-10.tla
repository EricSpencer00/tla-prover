---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT N            \* Number of processes
CONSTANT T            \* Maximum number of tolerated faults
CONSTANT F            \* Maximum number of actual crashes
CONSTANT Values       \* Finite set of proposal values (totally ordered)
CONSTANT Bottom       \* Special bottom value, not in Values

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
Assumption_F_T_Bounds == /\ 0 <= F /\ F <= T /\ 2 * T < N

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Proc == 1..N
Value == Values \cup {Bottom}
MsgType == {"p1", "p2"}

Message == [type : MsgType,
            sender : Proc,
            propVal : Value,
            estVal : Value \ {Bottom} ]   \* estVal defined only for p2

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    pc,               \* control location of each process
    view,             \* N-by-N matrix of received proposal values
    prop,             \* each process's own proposed value
    est,              \* each process's estimated value (max of view)
    dec,              \* decision value of each process (or Bottom)
    crashed,          \* set of crashed processes
    sent,             \* set of messages that have been sent
    recv              \* received messages per process (set of Message)

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Locs == {"bcast1", "wait1", "bcast2", "wait2",
         "choosing", "done", "crashed"}

MaxInView(p) == 
    LET vals == { view[p][q] : q \in Proc } \ {Bottom} IN
    IF vals = {} THEN Bottom ELSE CHOOSE v \in vals : 
        \A w \in vals : v >= w

CountReceived(p, typ) ==
    Cardinality({ m \in recv[p] : m.type = typ })

CountEst(p, v) ==
    Cardinality({ m \in recv[p] : /\ m.type = "p2"
                               /\ m.estVal = v })

AllSenders(p) ==
    { m.sender : m \in recv[p] }

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ prop \in [p \in Proc |-> Values]             \* each proposes a value
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ Cardinality(crashed) < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

Bcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ sent' = sent \cup { [type |-> "p1",
                           sender |-> p,
                           propVal |-> prop[p],
                           estVal |-> Bottom] }
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

Recv1(p) ==
    /\ pc[p] = "wait1"
    /\ \E m \in sent :
        /\ m.type = "p1"
        /\ m.sender \notin crashed
        /\ m.sender \notin { mm.sender : mm \in recv[p] }
        /\ view' = [view EXCEPT ![p][m.sender] = m.propVal]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ CountReceived(p, "p1") >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInView(p)]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

Bcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ sent' = sent \cup { [type |-> "p2",
                           sender |-> p,
                           propVal |-> prop[p],
                           estVal |-> est[p]] }
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

Recv2(p) ==
    /\ pc[p] = "wait2"
    /\ \E m \in sent :
        /\ m.type = "p2"
        /\ m.sender \notin crashed
        /\ m.sender \notin { mm.sender : mm \in recv[p] }
        /\ view' = [view EXCEPT ![p][m.sender] = m.propVal]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

DecideIfThreshold(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
        /\ CountEst(p, v) >= N - T
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ CountReceived(p, "p2") = N
    /\ \A v \in Values : CountEst(p, v) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent, recv>>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ \E v \in Values :
        /\ v \in { view[p][q] : q \in Proc }
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in Proc : Crash(p)
    \/ \E p \in Proc : Bcast1(p)
    \/ \E p \in Proc : Recv1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : Bcast2(p)
    \/ \E p \in Proc : Recv2(p)
    \/ \E p \in Proc : DecideIfThreshold(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, view, prop, est, dec, crashed, sent, recv>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> Locs]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Value]]
    /\ est \in [Proc -> Value]
    /\ dec \in [Proc -> Value]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

Validity ==
    \A p \in Proc :
        (dec[p] # Bottom) => (\E q \in Proc : prop[q] = dec[p])

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

=============================================================================