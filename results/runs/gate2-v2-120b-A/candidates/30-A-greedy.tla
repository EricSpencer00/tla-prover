---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N
Value == Values \cup {Bottom}
MsgType == {"Phase1", "Phase2"}

\* ----------------------------------------------------------------------
\* Message record
\* ----------------------------------------------------------------------
Message == [type : MsgType,
            sender : Proc,
            prop : Value,
            est : Value] \* est = Bottom for Phase1 messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location per process
          prop,             \* proposed value per process
          view,             \* N-by-N matrix of received values
          est,              \* estimated value per process
          dec,              \* decision value per process
          crashed,          \* set of crashed processes
          sent,             \* set of all sent messages
          recv              \* set of messages received per process

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Locs == {"Broadcast1", "Wait1", "Broadcast2", "Wait2",
         "Done", "Crashed", "Choosing"}

Max(vs) == 
  IF \E x \in vs : x # Bottom
  THEN CHOOSE x \in vs : \A y \in vs : (y # Bottom) => y <= x
  ELSE Bottom

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "Broadcast1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE] \* any value from Values
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "Broadcast1"
  /\ sent' = sent \cup {[type |-> "Phase1",
                         sender |-> p,
                         prop |-> prop[p],
                         est |-> Bottom]}
  /\ pc' = [pc EXCEPT ![p] = "Wait1"]
  /\ UNCHANGED <<prop, view, est, dec, crashed, recv>>

Receive1(p) ==
  /\ pc[p] = "Wait1"
  /\ \E m \in sent :
        /\ m.type = "Phase1"
        /\ m.sender \notin crashed
        /\ m.sender \notin recv[p]
        /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

ComputeEst(p) ==
  /\ pc[p] = "Wait1"
  /\ Cardinality({ s \in Proc : view[p][s] # Bottom }) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][s] : s \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "Broadcast2"]
  /\ UNCHANGED <<prop, view, dec, crashed, sent, recv>>

Broadcast2(p) ==
  /\ pc[p] = "Broadcast2"
  /\ sent' = sent \cup {[type |-> "Phase2",
                         sender |-> p,
                         prop |-> prop[p],
                         est |-> est[p]]}
  /\ pc' = [pc EXCEPT ![p] = "Wait2"]
  /\ UNCHANGED <<prop, view, est, dec, crashed, recv>>

Receive2(p) ==
  /\ pc[p] = "Wait2"
  /\ \E m \in sent :
        /\ m.type = "Phase2"
        /\ m.sender \notin crashed
        /\ m.sender \notin recv[p]
        /\ view' = [view EXCEPT ![p][m.sender] = m.est]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

DecideFromEst(p) ==
  /\ pc[p] = "Wait2"
  /\ \E v \in Values :
        /\ Cardinality({ m \in recv[p] : m.type = "Phase2" /\ m.est = v }) >= N - T
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "Done"]
  /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

MoveToChoosing(p) ==
  /\ pc[p] = "Wait2"
  /\ Cardinality({ m \in recv[p] : m.type = "Phase2" }) = N
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] : m.type = "Phase2" /\ m.est = v }) < N - T
  /\ pc' = [pc EXCEPT ![p] = "Choosing"]
  /\ UNCHANGED <<prop, view, est, dec, crashed, sent, recv>>

Choose(p) ==
  /\ pc[p] = "Choosing"
  /\ \E v \in Values :
        /\ v \in { view[p][q] : q \in Proc }
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "Done"]
  /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

Crash(p) ==
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ crashed' = crashed \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "Crashed"]
  /\ UNCHANGED <<prop, view, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p \in Proc : Receive1(p)
  \/ \E p \in Proc : ComputeEst(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ \E p \in Proc : Receive2(p)
  \/ \E p \in Proc : DecideFromEst(p)
  \/ \E p \in Proc : MoveToChoosing(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, prop, view, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> Locs]
  /\ prop \in [Proc -> Values]
  /\ view \in [Proc -> [Proc -> Value]]
  /\ est \in [Proc -> Value]
  /\ dec \in [Proc -> Value]
  /\ crashed \subseteq Proc
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    dec[p] # Bottom => dec[p] \in Values

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====