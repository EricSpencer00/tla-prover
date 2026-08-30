---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* Conditions from the spec: 2*T < N, 0 <= F <= T, N > 0.
ASSUME /\ 2 * T < N
       /\ 0 <= F /\ F <= T
       /\ N > 0
       /\ Bottom \notin Values
       /\ Values # {}

Processes == 0..(N - 1)

VARIABLES loc, view, prop, estimate, decided, crashedCount, messages, received

vars == <<loc, view, prop, estimate, decided, crashedCount, messages, received>>

\* Phase-1 messages carry just a value; Phase-2 messages also carry an estimate.
Message == [type: 1..2, val: Values \cup {Bottom}, est: Values \cup {Bottom}, src: Processes]

Majority == Cardinality(Processes) \div 2 + 1

TypeOK ==
  /\ loc \in [Processes -> {"p1b", "p1w", "p2b", "p2w", "done", "crashed", "choose"}]
  /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
  /\ prop \in [Processes -> Values]
  /\ estimate \in [Processes -> Values \cup {Bottom}]
  /\ decided \in [Processes -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ messages \subseteq Message
  /\ received \in [Processes -> SUBSET Message]

\* The estimated value is always the maximum the process has observed.
Consistent == \A p \in Processes :
               (estimate[p] # Bottom) =>
                 \A q \in Processes :
                   /\ view[p][q] # Bottom => view[p][q] <= estimate[p]
                   /\ (q \notin received[p] \/ p = q \/ q \in {m.src : m \in received[p]})

Init ==
  /\ loc = [p \in Processes |-> "p1b"]
  /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
  /\ prop \in [Processes -> Values]
  /\ estimate = [p \in Processes |-> Bottom]
  /\ decided = [p \in Processes |-> Bottom]
  /\ crashedCount = 0
  /\ messages = {}
  /\ received = [p \in Processes |-> {}]

Send(m) == messages' = messages \cup {m}

\* A process may crash at any time; at most F ever do so.
Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, estimate, decided, messages, received>>

BroadcastP1(p) ==
  /\ loc[p] = "p1b"
  /\ Send([type |-> 1, val |-> prop[p], est |-> Bottom, src |-> p])
  /\ loc' = [loc EXCEPT ![p] = "p1w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashedCount, messages, received>>

ReceiveP1(p, m) ==
  /\ loc[p] = "p1w"
  /\ m \in messages
  /\ m.type = 1
  /\ p \notin received[m.src]
  /\ view' = [view EXCEPT ![p][m.src] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashedCount, messages>>

\* The estimate is the maximum observed value, so a process proposing the
\* global maximum keeps that maximum once it adopts its own view.
Compute(p) ==
  /\ loc[p] = "p1w"
  /\ Cardinality({m \in received[p] : m.type = 1}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] =
        IF \E q \in Processes : view[p][q] = CHOOSE x \in Values : \A r \in Processes :
                                view[p][r] # Bottom => view[p][r] <= x
         THEN CHOOSE x \in Values : \A r \in Processes :
                  view[p][r] # Bottom => view[p][r] <= x
         ELSE Bottom]
  /\ loc' = [loc EXCEPT ![p] = "p2b"]
  /\ UNCHANGED <<view, prop, decided, crashedCount, messages, received>>

BroadcastP2(p) ==
  /\ loc[p] = "p2b"
  /\ Send([type |-> 2, val |-> prop[p], est |-> estimate[p], src |-> p])
  /\ loc' = [loc EXCEPT ![p] = "p2w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashedCount, messages, received>>

ReceiveP2(p, m) ==
  /\ loc[p] = "p2w"
  /\ m \in messages
  /\ m.type = 2
  /\ p \notin received[m.src]
  /\ view' = [view EXCEPT ![p][m.src] = m.val]
  /\ estimate' = [estimate EXCEPT ![p][m.src] = m.est]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, decided, crashedCount, messages>>

\* The Count-based decision is exactly the condition that can be satisfied by
\* a minority (F+1 out of N) if the minority is the sole proposer of the max.
Decide(p) ==
  /\ loc[p] = "p2w"
  /\ Cardinality({m \in received[p] : m.type = 2 /\ m.est = estimate[p]}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashedCount, messages, received>>

Choose(p) ==
  /\ loc[p] = "p2w"
  /\ Cardinality({m \in received[p] : m.type = 2}) = N
  /\ Cardinality({m \in received[p] : m.type = 2 /\ m.est = estimate[p]}) < N - T
  /\ \E q \in Processes : view[p][q] # Bottom
  /\ decided' = [decided EXCEPT ![p] = view[p][CHOOSE q \in Processes : view[p][q] # Bottom]]
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, crashedCount, messages, received>>

Quiesce == \A p \in Processes : loc[p] \in {"done", "crashed"}

Next ==
  \/ \E p \in Processes : Crash(p) \/ BroadcastP1(p) \/ Compute(p) \/ BroadcastP2(p) \/ Decide(p) \/ Choose(p)
  \/ \E p \in Processes, m \in Message : ReceiveP1(p, m) \/ ReceiveP2(p, m)
  \/ Quiesce

\* Fairness: a process that can receive keeps receiving, and the choice is
\* strongly fair so it cannot be postponed forever.
Spec == Init /\ [][Next]_vars
            /\ \A p \in Processes :
                 /\ WF_vars(\E m \in Message : ReceiveP1(p, m))
                 /\ WF_vars(\E m \in Message : ReceiveP2(p, m))
                 /\ SF_vars(Decide(p) \/ Choose(p))

Validity == \A p \in Processes : decided[p] # Bottom => \E q \in Processes : prop[q] = decided[p]

Agreement == \A p1 \in Processes, p2 \in Processes :
               (decided[p1] # Bottom /\ decided[p2] # Bottom) => decided[p1] = decided[p2]

\* Conditional termination: with at least F+1 proposals equal to the maximum,
\* the Count-based condition C1 is satisfied from the start.
Termination == Quiesce
ConditionalTermination == (\E q \in Processes : prop[q] = CHOOSE x \in Values : \A q2 \in Processes : prop[q2] <= x) => Quiesce

====