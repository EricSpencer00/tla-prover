---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Assumptions on the constants
\* ----------------------------------------------------------------------
ASSUME N > 0
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME Bottom \notin Values
ASSUME Values \subseteq Nat

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"p1", "p2"},
            sender : Proc,
            value  : Values,
            est    : Values]   \* For phase‑1 messages est = Bottom

Max(S) == IF S = {} THEN Bottom
         ELSE CHOOSE v \in S : \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, crashedCount, Sent, Recv

vars == << pc, view, prop, est, dec, crashedCount, Sent, Recv >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ prop \in [Proc -> Values]                \* each process chooses a proposal
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ Sent = {}
    /\ Recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ LET m == [type |-> "p1",
                 sender |-> p,
                 value |-> prop[p],
                 est   |-> Bottom] IN
       Sent' = Sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, Recv >>

ReceivePhase1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in Sent
    /\ m.type = "p1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ Recv' = [Recv EXCEPT ![p] = Recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, Sent >>

ComputeAndBroadcast(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality({s \in Proc : view[p][s] # Bottom}) >= N - T
    /\ LET estVal == Max({view[p][s] : s \in Proc /\ view[p][s] # Bottom}) IN
          est' = [est EXCEPT ![p] = estVal] /\
          LET m == [type |-> "p2",
                    sender |-> p,
                    value |-> prop[p],
                    est   |-> estVal] IN
              Sent' = Sent \cup {m} /\
          pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED << view, prop, dec, crashedCount, Recv >>

ReceivePhase2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in Sent
    /\ m.type = "p2"
    /\ Recv' = [Recv EXCEPT ![p] = Recv[p] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, Sent >>

Decide(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Values :
          Cardinality({m \in Recv[p] : m.type = "p2" /\ m.est = v}) >= N - T
    /\ LET v == CHOOSE w \in Values :
            Cardinality({m \in Recv[p] : m.type = "p2" /\ m.est = w}) >= N - T IN
          dec' = [dec EXCEPT ![p] = v] /\
          pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, Sent, Recv >>

MoveToChoosing(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality({m \in Recv[p] : m.type = "p2"}) = N
    /\ \A v \in Values :
          Cardinality({m \in Recv[p] : m.type = "p2" /\ m.est = v}) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, Sent, Recv >>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ \E v \in Values : v \in {view[p][s] : s \in Proc}
    /\ LET v == CHOOSE w \in Values : w \in {view[p][s] : s \in Proc} IN
          dec' = [dec EXCEPT ![p] = v] /\
          pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, Sent, Recv >>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << view, prop, est, dec, Sent, Recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in Sent : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeAndBroadcast(p)
    \/ \E p \in Proc, m \in Sent : ReceivePhase2(p, m)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values]
    /\ dec \in [Proc -> Values]
    /\ crashedCount \in Nat
    /\ Sent \subseteq Message
    /\ Recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => (\E q \in Proc : prop[q] = dec[p])

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
\* (already defined: Spec, TypeOK, Validity, Agreement)

====