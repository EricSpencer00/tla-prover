---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat \setminus {0}
       /\ T \in Nat
       /\ F \in Nat
       /\ 2 * T < N
       /\ F <= T
       /\ Bottom \notin Values
       /\ Values \subseteq Nat   \* assume a total order via Nat

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
PROC == 1..N

\* ----------------------------------------------------------------------
\* Message type
\* ----------------------------------------------------------------------
Message == [type : {"p1","p2"},
            sender : PROC,
            val : Values,
            est : (Values \cup {Bottom})]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* N×N matrix of received values (phase 1)
          viewEst,          \* N×N matrix of received estimated values (phase 2)
          prop,             \* proposed value of each process
          est,              \* estimated value after phase 1
          dec,              \* decision value
          sent,             \* set of messages that have been broadcast
          crashedCount      \* number of crashed processes

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) == 
  CHOOSE x \in S : \A y \in S : y <= x

Estimation(p) ==
  LET vals == { view[p][q] : q \in PROC /\ view[p][q] # Bottom } IN
  IF vals = {} THEN Bottom ELSE Max(vals)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in PROC |-> "broadcast1"]
  /\ prop \in [PROC -> Values]
  /\ view = [p \in PROC |-> [q \in PROC |-> Bottom]]
  /\ viewEst = [p \in PROC |-> [q \in PROC |-> Bottom]]
  /\ est = [p \in PROC |-> Bottom]
  /\ dec = [p \in PROC |-> Bottom]
  /\ sent = {}
  /\ crashedCount = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "broadcast1"
  /\ sent' = sent \cup { [type |-> "p1", sender |-> p,
                         val |-> prop[p], est |-> Bottom] }
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED << view, viewEst, prop, est, dec, crashedCount >>

Recv1(p, m) ==
  /\ pc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "p1"
  /\ view' = [view EXCEPT ![p] = [view[p] EXCEPT ![m.sender] = m.val]]
  /\ UNCHANGED << pc, viewEst, prop, est, dec, sent, crashedCount >>

ComputeEst(p) ==
  /\ pc[p] = "wait1"
  /\ Cardinality({ q \in PROC : view[p][q] # Bottom }) >= N - T
  /\ est' = [est EXCEPT ![p] = Estimation(p)]
  /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED << view, viewEst, prop, dec, sent, crashedCount >>

Broadcast2(p) ==
  /\ pc[p] = "broadcast2"
  /\ sent' = sent \cup { [type |-> "p2", sender |-> p,
                         val |-> prop[p], est |-> est[p]] }
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED << view, viewEst, prop, est, dec, crashedCount >>

Recv2(p, m) ==
  /\ pc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "p2"
  /\ viewEst' = [viewEst EXCEPT ![p] = [viewEst[p] EXCEPT ![m.sender] = m.est]]
  /\ UNCHANGED << pc, view, prop, est, dec, sent, crashedCount >>

Decide(p) ==
  /\ pc[p] = "wait2"
  /\ \E v \in Values :
        Cardinality({ q \in PROC : viewEst[p][q] = v }) >= N - T
  /\ LET v == CHOOSE v \in Values :
        Cardinality({ q \in PROC : viewEst[p][q] = v }) >= N - T
     IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, viewEst, prop, est, sent, crashedCount >>

MoveToChoosing(p) ==
  /\ pc[p] = "wait2"
  /\ \A v \in Values :
        Cardinality({ q \in PROC : viewEst[p][q] = v }) < N - T
  /\ Cardinality({ q \in PROC : viewEst[p][q] # Bottom }) = N
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, viewEst, prop, est, dec, sent, crashedCount >>

Choosing(p) ==
  /\ pc[p] = "choosing"
  /\ LET vals == { view[p][q] : q \in PROC /\ view[p][q] # Bottom } IN
        vals /= {}
  /\ LET v == CHOOSE x \in vals : TRUE
     IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, viewEst, prop, est, sent, crashedCount >>

Crash(p) ==
  /\ pc[p] \notin {"crashed","done"}
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, viewEst, prop, est, dec, sent >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
 \/ \E p \in PROC : Broadcast1(p)
 \/ \E p \in PROC, m \in sent : Recv1(p,m)
 \/ \E p \in PROC : ComputeEst(p)
 \/ \E p \in PROC : Broadcast2(p)
 \/ \E p \in PROC, m \in sent : Recv2(p,m)
 \/ \E p \in PROC : Decide(p)
 \/ \E p \in PROC : MoveToChoosing(p)
 \/ \E p \in PROC : Choosing(p)
 \/ \E p \in PROC : Crash(p)
 \/ UNCHANGED << pc, view, viewEst, prop, est, dec, sent, crashedCount >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << pc, view, viewEst, prop, est, dec, sent, crashedCount >>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
 /\ pc \in [PROC -> {"broadcast1","wait1","broadcast2","wait2","done","crashed","choosing"}]
 /\ view \in [PROC -> [PROC -> (Values \cup {Bottom})]]
 /\ viewEst \in [PROC -> [PROC -> (Values \cup {Bottom})]]
 /\ prop \in [PROC -> Values]
 /\ est \in [PROC -> (Values \cup {Bottom})]
 /\ dec \in [PROC -> (Values \cup {Bottom})]
 /\ sent \subseteq Message
 /\ crashedCount \in Nat

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
 \A p \in PROC :
   dec[p] # Bottom => \E q \in PROC : prop[q] = dec[p]

Agreement ==
 \A p,q \in PROC :
   (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

====