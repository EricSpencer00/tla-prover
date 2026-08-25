---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* -----------------------------------------------------------------
\* Derived sets
Proc == 1..N

ControlLoc == {"b1", "w1", "b2", "w2", "done", "crashed", "choose"}

Message == [type : {"phase1", "phase2"},
            val  : Values,
            est  : Values \cup {Bottom},
            sender : Proc]

\* -----------------------------------------------------------------
\* Variables
VARIABLES pc, view, prop, est, dec, crashedCount, sent, recvd

vars == << pc, view, prop, est, dec, crashedCount, sent, recvd >>

\* -----------------------------------------------------------------
\* Helper definitions
Max(S) == 
    IF S = {} 
    THEN Bottom 
    ELSE CHOOSE x \in S : \A y \in S : y <= x

ReceivedFrom(p, phase) ==
    { m \in recvd[p] : m.type = phase }

\* -----------------------------------------------------------------
\* Initial state
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recvd = [p \in Proc |-> {}]

\* -----------------------------------------------------------------
\* Actions

Broadcast1(p) ==
    /\ pc[p] = "b1"
    /\ LET m == [type |-> "phase1",
                 val  |-> prop[p],
                 est  |-> Bottom,
                 sender |-> p]
       IN sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recvd >>

Broadcast2(p) ==
    /\ pc[p] = "b2"
    /\ LET m == [type |-> "phase2",
                 val  |-> prop[p],
                 est  |-> est[p],
                 sender |-> p]
       IN sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recvd >>

Receive1(p) ==
    /\ pc[p] = "w1"
    /\ \E m \in sent :
          /\ m.type = "phase1"
          /\ m \notin recvd[p]
          /\ view' = [view EXCEPT ![p][m.sender] = m.val]
          /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

Receive2(p) ==
    /\ pc[p] = "w2"
    /\ \E m \in sent :
          /\ m.type = "phase2"
          /\ m \notin recvd[p]
          /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, sent >>

ComputeEst(p) ==
    /\ pc[p] = "w1"
    /\ LET receivedSenders == { q \in Proc : view[p][q] # Bottom }
       IN Cardinality(receivedSenders) >= N - T
    /\ est' = [est EXCEPT ![p] = 
                Max({ view[p][q] : q \in Proc /\ view[p][q] # Bottom })]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED << view, prop, dec, crashedCount, sent, recvd >>

Decide(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Values :
          /\ Cardinality({ m \in recvd[p] : 
                           m.type = "phase2" /\ m.est = v }) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recvd >>

MoveToChoose(p) ==
    /\ pc[p] = "w2"
    /\ LET phase2Msgs == { m \in recvd[p] : m.type = "phase2" }
           senders    == { m.sender : m \in phase2Msgs }
       IN /\ Cardinality(senders) = N
          /\ \A v \in Values :
               Cardinality({ m \in phase2Msgs : m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recvd >>

Choose(p) ==
    /\ pc[p] = "choose"
    /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }
          val == CHOOSE x \in candidates : TRUE
       IN dec' = [dec EXCEPT ![p] = val]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recvd >>

Crash(p) ==
    /\ crashedCount < F
    /\ pc[p] # "crashed"
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << view, prop, est, dec, sent, recvd >>

\* -----------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in Proc : Broadcast1(p)
    \/ \E p \in Proc : Receive1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : Broadcast2(p)
    \/ \E p \in Proc : Receive2(p)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : MoveToChoose(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* -----------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ pc \in [Proc -> ControlLoc]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recvd \in [Proc -> SUBSET sent]

\* -----------------------------------------------------------------
\* Safety properties
Validity ==
    \A p \in Proc :
        dec[p] = Bottom
        \/ dec[p] \in { prop[q] : q \in Proc }

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* -----------------------------------------------------------------
\* Invariants list for the model checker
INVARIANTS == TypeOK /\ Validity /\ Agreement

====