---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1 .. N
PhaseType == {"phase1", "phase2"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          prop,             \* proposed value of each process
          view,             \* N->(N->Values) matrix of received values
          est,              \* estimated value after phase 1
          dec,              \* decision value (Bottom if not decided)
          crashed,          \* set of crashed processes
          msgs,             \* set of all sent messages
          rcv               \* N-> SUBSET msgs: messages received by each proc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Message == [type : PhaseType,
            sender : Proc,
            value : Values,
            est : Values]   \* for phase2 messages the field `est` holds the estimated value

Max(S) == 
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : v >= w

ReceivedPhase1(p) == { m \in rcv[p] : m.type = "phase1" }
ReceivedPhase2(p) == { m \in rcv[p] : m.type = "phase2" }

CountEst(p, v) == Cardinality({ m \in ReceivedPhase2(p) : m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ prop \in [Proc -> Values]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ msgs = {}
  /\ rcv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ pc[p] = "b1"
  /\ UNCHANGED <<prop, view, est, dec, crashed, rcv>>
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ msgs' = msgs \cup { [type |-> "phase1",
                         sender |-> p,
                         value  |-> prop[p],
                         est    |-> Bottom] }
  /\ UNCHANGED <<pc, prop, view, est, dec, crashed, rcv>>

ReceivePhase1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in msgs
  /\ m.type = "phase1"
  /\ ~(\E mm \in rcv[p] : mm.sender = m.sender)   \* not already received
  /\ pc' = pc
  /\ msgs' = msgs
  /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ UNCHANGED <<prop, est, dec, crashed>>

ComputeEst(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(ReceivedPhase1(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
  /\ UNCHANGED <<prop, view, dec, crashed, msgs, rcv>>

BroadcastPhase2(p) ==
  /\ pc[p] = "b2"
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ msgs' = msgs \cup { [type |-> "phase2",
                         sender |-> p,
                         value  |-> prop[p],
                         est    |-> est[p]] }
  /\ UNCHANGED <<prop, view, est, dec, crashed, rcv>>

ReceivePhase2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in msgs
  /\ m.type = "phase2"
  /\ ~(\E mm \in rcv[p] : mm.sender = m.sender)   \* not already received
  /\ pc' = pc
  /\ msgs' = msgs
  /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.est]
  /\ UNCHANGED <<prop, est, dec, crashed>>

Decide(p, v) ==
  /\ pc[p] = "w2"
  /\ v \in Values
  /\ CountEst(p, v) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ UNCHANGED <<prop, view, est, crashed, msgs, rcv>>

MoveToChoosing(p) ==
  /\ pc[p] = "w2"
  /\ Cardinality(ReceivedPhase2(p)) = N
  /\ \A v \in Values : CountEst(p, v) < N - T
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<prop, view, est, dec, crashed, msgs, rcv>>

Choose(p) ==
  /\ pc[p] = "choosing"
  /\ LET S == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
        S # {}
  /\ LET v == CHOOSE x \in S : TRUE IN
        /\ pc' = [pc EXCEPT ![p] = "done"]
        /\ dec' = [dec EXCEPT ![p] = v]
  /\ UNCHANGED <<prop, view, est, crashed, msgs, rcv>>

Crash(p) ==
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED <<prop, view, est, dec, msgs, rcv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ BroadcastPhase1(p)
    \/ \E m \in msgs : ReceivePhase1(p, m)
    \/ ComputeEst(p)
    \/ BroadcastPhase2(p)
    \/ \E m \in msgs : ReceivePhase2(p, m)
    \/ \E v \in Values : Decide(p, v)
    \/ MoveToChoosing(p)
    \/ Choose(p)
    \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<pc, view, prop, est, dec, crashed, msgs, rcv>>

Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ N \in Nat
  /\ T \in Nat
  /\ F \in Nat
  /\ 2 * T < N
  /\ 0 <= F /\ F <= T
  /\ Bottom \notin Values
  /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
  /\ prop \in [Proc -> Values]
  /\ view \in [Proc -> [Proc -> Values]]
  /\ est \in [Proc -> Values]
  /\ dec \in [Proc -> Values]
  /\ crashed \subseteq Proc
  /\ msgs \subseteq Message
  /\ rcv \in [Proc -> SUBSET msgs]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    dec[p] # Bottom => \E q \in Proc : prop[q] = dec[p]

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Invariants list (required by the .cfg file)
\* ----------------------------------------------------------------------
INVARIANT == TypeOK /\ Validity /\ Agreement

====