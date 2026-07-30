---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* A message carries the phase it belongs to so that an old-phase message
\* cannot be applied to a later-phase local view -- that is what bounds the
\* view growth and keeps the model finite.
Message == [phase: {1, 2}, val: Values, from: 1..N, est: Values \cup {Bottom}]

VARIABLES loc, seen, prop, est, decided, crashed, sent, recvBy

vars == <<loc, seen, prop, est, decided, crashed, sent, recvBy>>

Phases == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choose"}
MaxSeen(p) == CHOOSE x \in Values : \A q \in 1..N : seen[p][q] <= x

TypeOK ==
    /\ loc \in [1..N -> Phases]
    /\ seen \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Message
    /\ recvBy \in [1..N -> SUBSET Message]

Init ==
    /\ loc = [p \in 1..N |-> "broadcast1"]
    /\ seen = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ est = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recvBy = [p \in 1..N |-> {}]

\* Phase 2 messages also carry the sender's estimated value, because that is
\* what the receiver counts -- and not just the payload -- when it decides.
Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ sent' = sent \cup {[phase |-> 1, val |-> prop[p], from |-> p, est |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<seen, prop, est, decided, crashed, recvBy>>

Receive1(p, m) ==
    /\ loc[p] = "wait1"
    /\ m \in sent
    /\ m.phase = 1
    /\ m.from \notin {q.from : q \in recvBy[p]}
    /\ seen' = [seen EXCEPT ![p][m.from] = m.val]
    /\ recvBy' = [recvBy EXCEPT ![p] = recvBy[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decided, crashed, sent>>

\* The N-T bound on distinct senders is what makes the condition check
\* feasible; it is what distinguishes a reliable majority (quorum) here.
Estimate(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({q.from : q \in recvBy[p]}) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxSeen(p)]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<seen, prop, decided, crashed, sent, recvBy>>

Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ sent' = sent \cup {[phase |-> 2, val |-> prop[p], from |-> p, est |-> est[p]]}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<seen, prop, est, decided, crashed, recvBy>>

Receive2(p, m) ==
    /\ loc[p] = "wait2"
    /\ m \in sent
    /\ m.phase = 2
    /\ m.from \notin {q.from : q \in recvBy[p]}
    /\ seen' = [seen EXCEPT ![p][m.from] = m.val]
    /\ recvBy' = [recvBy EXCEPT ![p] = recvBy[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decided, crashed, sent>>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
         /\ Cardinality({m \in recvBy[p] : m.phase = 2 /\ m.est = v}) >= N - T
         /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<seen, prop, est, crashed, sent, recvBy>>

Choose(p) ==
    /\ loc[p] = "wait2"
    /\ \A m \in recvBy[p] : m.phase = 2
    /\ Cardinality({m.from | m \in recvBy[p]}) = N
    /\ \E v \in Values :
         decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<seen, prop, est, crashed, sent, recvBy>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<seen, prop, est, decided, sent, recvBy>>

Next ==
    \/ \E p \in 1..N : Broadcast1(p)
    \/ \E p \in 1..N, m \in Message : Receive1(p, m)
    \/ \E p \in 1..N : Estimate(p)
    \/ \E p \in 1..N : Broadcast2(p)
    \/ \E p \in 1..N, m \in Message : Receive2(p, m)
    \/ \E p \in 1..N : Decide(p)
    \/ \E p \in 1..N : Choose(p)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N, m \in Message : Receive1(p, m))
    /\ WF_vars(\E p \in 1..N, m \in Message : Receive2(p, m))
    /\ WF_vars(\E p \in 1..N : Estimate(p))
    /\ WF_vars(\E p \in 1..N : Choose(p))

Validity == \A p \in 1..N : decided[p] # Bottom => decided[p] \in {prop[q] : q \in 1..N}
Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]
Termination == <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})
ConditionalTermination == MaxValues >= F + 1 => <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})
MaxValues == Cardinality({i \in 1..N : prop[i] = CHOOSE m \in Values : \A j \in 1..N : prop[j] <= m})

====