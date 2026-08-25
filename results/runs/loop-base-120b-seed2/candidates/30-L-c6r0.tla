---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    N,                \* number of processes
    T,                \* tolerance parameter (2*T < N)
    F,                \* maximum number of actual crashes
    Values,           \* finite totally ordered set of proposed values
    Bottom            \* special bottom value, not in Values

\* ----------------------------------------------------------------------
\* Basic sets
Proc   == 1 .. N
Locs   == {"bcast1", "wait1", "bcast2", "wait2", "done", "crashed", "choosing"}
MsgType == {"phase1", "phase2"}

\* ----------------------------------------------------------------------
\* Message definition
Message == [type : MsgType,
            sender : Proc,
            val   : Values,
            est   : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    loc,          \* [p \in Proc -> Locs]
    view,         \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]
    prop,         \* [p \in Proc -> Values]          (initial proposals)
    est,          \* [p \in Proc -> Values \cup {Bottom}]
    decision,     \* [p \in Proc -> Values \cup {Bottom}]
    crashedCount, \* Nat
    sent,         \* SUBSET Message
    recv2         \* [p \in Proc -> SUBSET Message]   (phase‑2 messages received)

vars == << loc, view, prop, est, decision, crashedCount, sent, recv2 >>

\* ----------------------------------------------------------------------
\* Helper operators
DistinctSenders(v) == { s \in Proc : v[s] # Bottom }

MaxInSet(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* Count of messages in recv2[p] whose estimated value equals v
CountEst(p, v) == 
    Cardinality({ m \in recv2[p] : m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ loc = [p \in Proc |-> "bcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]               \* each process chooses a proposal
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv2 = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions

\* Phase‑1 broadcast
Bcast1(p) ==
    /\ loc[p] = "bcast1"
    /\ sent' = sent \cup { [type |-> "phase1", sender |-> p, val |-> prop[p], est |-> Bottom] }
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << view, prop, est, decision, crashedCount, recv2 >>

\* Phase‑1 receive
Recv1(p, m) ==
    /\ loc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ view[p][m.sender] = Bottom               \* not yet received from this sender
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ UNCHANGED << loc, prop, est, decision, crashedCount, sent, recv2 >>

\* After having enough phase‑1 messages, compute estimate and move to phase‑2 broadcast
ComputeEst(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality(DistinctSenders(view[p])) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInSet({ view[p][s] : s \in Proc } )]
    /\ loc' = [loc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED << view, prop, decision, crashedCount, sent, recv2 >>

\* Phase‑2 broadcast
Bcast2(p) ==
    /\ loc[p] = "bcast2"
    /\ sent' = sent \cup { [type |-> "phase2", sender |-> p,
                            val |-> prop[p], est |-> est[p]] }
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << view, prop, est, decision, crashedCount, recv2 >>

\* Phase‑2 receive
Recv2(p, m) ==
    /\ loc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ \A mm \in recv2[p] : mm.sender # m.sender    \* at most one from each sender
    /\ recv2' = [recv2 EXCEPT ![p] = recv2[p] \cup {m}]
    /\ UNCHANGED << loc, view, prop, est, decision, crashedCount, sent >>

\* Decide when a value appears in at least N‑T phase‑2 messages
Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values : CountEst(p, v) >= N - T
    /\ LET v == CHOOSE w \in Values : CountEst(p, w) >= N - T IN
          /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recv2 >>

\* If all N phase‑2 messages have been received but no value reaches the threshold,
\* move to the choosing state
MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({ m.sender : m \in recv2[p] }) = N
    /\ \A v \in Values : CountEst(p, v) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << view, prop, est, decision, crashedCount, sent, recv2 >>

\* Choose a value that appears in the local view (deterministically)
Choose(p) ==
    /\ loc[p] = "choosing"
    /\ LET candidates == { view[p][s] : s \in Proc /\ view[p][s] # Bottom } IN
          /\ candidates # {}
    /\ decision' = [decision EXCEPT ![p] = CHOOSE w \in candidates : TRUE ]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recv2 >>

\* Crash a process (as long as fewer than F have crashed)
Crash(p) ==
    /\ loc[p] # "crashed"
    /\ crashedCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << view, prop, est, decision, sent, recv2 >>

\* The next-state relation is the disjunction of all possible actions
Next ==
    \E p \in Proc :
        \/ Bcast1(p)
        \/ \E m \in sent : Recv1(p, m)
        \/ ComputeEst(p)
        \/ Bcast2(p)
        \/ \E m \in sent : Recv2(p, m)
        \/ Decide(p)
        \/ MoveToChoosing(p)
        \/ Choose(p)
        \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv2 \in [Proc -> SUBSET Message]
    /\ \A m \in sent :
          (m.type = "phase1" => m.est = Bottom) /\ 
          (m.type = "phase2" => m.est \in (Values \cup {Bottom}))
    /\ 2 * T < N
    /\ 0 <= F /\ F <= T
    /\ N > 0
    /\ Bottom \notin Values

\* ----------------------------------------------------------------------
\* Safety properties

\* Validity: every decided value was proposed by some process
Validity ==
    \A p \in Proc :
        (decision[p] # Bottom) => 
            \E q \in Proc : prop[q] = decision[p]

\* Agreement: no two processes decide different values
Agreement ==
    \A p, q \in Proc :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
THEOREM TypeOKInv == Spec => []TypeOK
THEOREM ValidityInv == Spec => []Validity
THEOREM AgreementInv == Spec => []Agreement

====