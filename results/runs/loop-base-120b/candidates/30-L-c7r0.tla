---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME 0 < N
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T

VARIABLES loc, view, prop, est, dec, crashed, sent, recvEst

Proc == 1..N
Locs == {"broadcast1", "wait1", "broadcast2", "wait2", "done", "crashed", "choosing"}

Message == [type   : {"phase1", "phase2"},
            value  : Values,
            sender : Proc,
            est    : Values \cup {Bottom}]

Init ==
    /\ loc     = [p \in Proc |-> "broadcast1"]
    /\ prop    = [p \in Proc |-> CHOOSE v \in Values : TRUE]
    /\ view    = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est     = [p \in Proc |-> Bottom]
    /\ dec     = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent    = {}
    /\ recvEst = [p \in Proc |-> [q \in Proc |-> Bottom]]

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
ReceivedPhase1(p) == { q \in Proc : view[p][q] # Bottom }

CountSameEst(p, v) ==
    Cardinality({ q \in Proc : recvEst[p][q] = v })

ReceivedAllPhase2(p) ==
    { q \in Proc : recvEst[p][q] # Bottom } = Proc

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ loc[p] = "broadcast1"
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ let m == [type |-> "phase1",
                value |-> prop[p],
                sender |-> p,
                est |-> Bottom] in
          sent' = sent \cup {m}
    /\ UNCHANGED <<view, prop, est, dec, crashed, recvEst>>

ReceivePhase1(p, m) ==
    /\ loc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ view[p][m.sender] = Bottom
    /\ loc' = loc
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ UNCHANGED <<prop, est, dec, crashed, sent, recvEst>>

ComputeEst(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality(ReceivedPhase1(p)) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recvEst>>

BroadcastPhase2(p) ==
    /\ loc[p] = "broadcast2"
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ let m == [type |-> "phase2",
                value |-> prop[p],
                sender |-> p,
                est |-> est[p]] in
          sent' = sent \cup {m}
    /\ UNCHANGED <<view, prop, est, dec, crashed, recvEst>>

ReceivePhase2(p, m) ==
    /\ loc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ recvEst[p][m.sender] = Bottom
    /\ loc' = loc
    /\ recvEst' = [recvEst EXCEPT ![p][m.sender] = m.est]
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent>>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values : CountSameEst(p, v) >= N - T
    /\ LET v == CHOOSE w \in Values : CountSameEst(p, w) >= N - T IN
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recvEst>>

MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ \A v \in Values : CountSameEst(p, v) < N - T
    /\ ReceivedAllPhase2(p)
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent, recvEst>>

Choose(p) ==
    /\ loc[p] = "choosing"
    /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
          /\ candidates # {}
    /\ LET v == CHOOSE w \in candidates : TRUE IN
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recvEst>>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<view, prop, est, dec, sent, recvEst>>

Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase2(p, m)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

Spec == Init /\ [][Next]_<<loc, view, prop, est, dec, crashed, sent, recvEst>>

\* -----------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------
TypeOK ==
    /\ loc     \in [Proc -> Locs]
    /\ view    \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ prop    \in [Proc -> Values]
    /\ est     \in [Proc -> Values \cup {Bottom}]
    /\ dec     \in [Proc -> Values \cup {Bottom}]
    /\ crashed \subseteq Proc
    /\ sent    \subseteq Message
    /\ recvEst \in [Proc -> [Proc -> Values \cup {Bottom}]]

Validity ==
    \A p \in Proc : dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

=============================================================================