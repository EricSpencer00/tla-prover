---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ F \in Nat /\ 2 * T < N /\ F <= T

Phases == {"bph1", "wph1", "prep", "bph2", "wph2", "done", "crashed", "choosing"}

Message == [kind : {"phase1", "phase2"}, val : Values, est : Values \cup {Bottom}, from : 0..(N - 1)]

VARIABLES location, view, proposed, estimate, decided, crashedCount, sent, received

vars == <<location, view, proposed, estimate, decided, crashedCount, sent, received>>

TypeOK ==
    /\ location \in [0..(N - 1) -> Phases]
    /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
    /\ proposed \in [0..(N - 1) -> Values]
    /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ crashedCount \in 0..F
    /\ sent \subseteq Message
    /\ received \in [0..(N - 1) -> SUBSET Message]

Init ==
    /\ location = [n \in 0..(N - 1) |-> "bph1"]
    /\ view = [n \in 0..(N - 1) |-> [m \in 0..(N - 1) |-> Bottom]]
    /\ proposed \in [0..(N - 1) -> Values]
    /\ estimate = [n \in 0..(N - 1) |-> Bottom]
    /\ decided = [n \in 0..(N - 1) |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ received = [n \in 0..(N - 1) |-> {}]

Bump ==
    /\ \E n \in 0..(N - 1) : location[n] = "crashed"
    /\ crashedCount < F
    /\ location' = [n \in 0..(N - 1) |->
         IF \E m \in 0..(N - 1) : location[m] = "crashed" /\ m # n
         THEN location[n] ELSE "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, proposed, estimate, decided, sent, received>>

\* Phase 1: broadcast the proposed value.
BroadcastP1 ==
    /\ \E n \in 0..(N - 1) :
         /\ location[n] = "bph1"
         /\ sent' = sent \cup {[kind |-> "phase1", val |-> proposed[n], est |-> Bottom, from |-> n]}
         /\ location' = [location EXCEPT ![n] = "wph1"]
    /\ UNCHANGED <<view, proposed, estimate, decided, crashedCount, received>>

ReceiveP1 ==
    /\ \E n \in 0..(N - 1), m \in Message :
         /\ location[n] = "wph1"
         /\ m \in sent
         /\ m.kind = "phase1"
         /\ m.from # n
         /\ m.val # Bottom
         /\ view' = [view EXCEPT ![n][m.from] = m.val]
         /\ received' = [received EXCEPT ![n] = received[n] \cup {m}]
    /\ UNCHANGED <<location, proposed, estimate, decided, crashedCount, sent>>

\* Phase 1 complete: estimate the maximum from the view and move to phase 2.
Prepare ==
    /\ \E n \in 0..(N - 1) :
         /\ location[n] = "wph1"
         /\ Cardinality({m \in 0..(N - 1) : view[n][m] # Bottom}) >= N - T
         /\ estimate' = [estimate EXCEPT ![n] = CHOOSE v \in Values :
                             \A m \in 0..(N - 1) : view[n][m] # Bottom => view[n][m] <= v]
         /\ location' = [location EXCEPT ![n] = "bph2"]
    /\ UNCHANGED <<view, proposed, decided, crashedCount, sent, received>>

\* Phase 2: broadcast both the proposed value and the estimated maximum.
BroadcastP2 ==
    /\ \E n \in 0..(N - 1) :
         /\ location[n] = "bph2"
         /\ sent' = sent \cup {[kind |-> "phase2", val |-> proposed[n], est |-> estimate[n], from |-> n]}
         /\ location' = [location EXCEPT ![n] = "wph2"]
    /\ UNCHANGED <<view, proposed, estimate, decided, crashedCount, received>>

ReceiveP2 ==
    /\ \E n \in 0..(N - 1), m \in Message :
         /\ location[n] = "wph2"
         /\ m \in sent
         /\ m.kind = "phase2"
         /\ m.from # n
         /\ m.val # Bottom
         /\ m.est # Bottom
         /\ view' = [view EXCEPT ![n][m.from] = m.val]
         /\ received' = [received EXCEPT ![n] = received[n] \cup {m}]
    /\ UNCHANGED <<location, proposed, estimate, decided, crashedCount, sent>>

\* Phase 2 complete: decide once a majority of the adjusted values agree.
Decide ==
    /\ \E n \in 0..(N - 1) :
         /\ location[n] = "wph2"
         /\ Cardinality({m \in received[n] : m.kind = "phase2"}) >= N - T
         /\ \E v \in Values :
              /\ Cardinality({m \in received[n] : m.kind = "phase2" /\ m.est = v}) >= N - T
              /\ decided' = [decided EXCEPT ![n] = v]
         /\ location' = [location EXCEPT ![n] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashedCount, sent, received>>

\* If phase 2 cannot reach the adjusted-value majority, fall back to choosing.
Choose ==
    /\ \E n \in 0..(N - 1) :
         /\ location[n] = "wph2"
         /\ \A v \in Values : Cardinality({m \in received[n] : m.kind = "phase2" /\ m.est = v}) < N - T
         /\ Cardinality({m \in received[n] : m.kind = "phase2"}) = N
         /\ location' = [location EXCEPT ![n] = "choosing"]
    /\ UNCHANGED <<view, proposed, estimate, decided, crashedCount, sent, received>>

FinishChoosing ==
    /\ \E n \in 0..(N - 1) :
         /\ location[n] = "choosing"
         /\ \E v \in Values :
              /\ \E m \in 0..(N - 1) : view[n][m] = v
              /\ decided' = [decided EXCEPT ![n] = v]
         /\ location' = [location EXCEPT ![n] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashedCount, sent, received>>

Next == Bump \/ BroadcastP1 \/ ReceiveP1 \/ Prepare \/ BroadcastP2
        \/ ReceiveP2 \/ Decide \/ Choose \/ FinishChoosing

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(BroadcastP1) /\ WF_vars(ReceiveP1) /\ WF_vars(Prepare)
    /\ WF_vars(BroadcastP2) /\ WF_vars(ReceiveP2) /\ WF_vars(Decide)
    /\ WF_vars(Choose) /\ WF_vars(FinishChoosing)

\* Any decided value must have been proposed by some process.
Validity == \A n \in 0..(N - 1) : decided[n] # Bottom => \E m \in 0..(N - 1) : proposed[m] = decided[n]

\* No two processes ever decide different values.
Agreement == \A a, b \in 0..(N - 1) : (decided[a] # Bottom /\ decided[b] # Bottom) => decided[a] = decided[b]

\* Every process eventually crashes or finishes with a decision.
Liveness == \A n \in 0..(N - 1) : (location[n] = "crashed") <~> (location[n] = "done")

\* Condition C1: if enough processes propose the global maximum, termination is
\* guaranteed (the pairwise agreement then pins that value as the sole outcome).
ConditionalTermination ==
    \A n \in 0..(N - 1) : (proposed[n] = CHOOSE v \in Values :
                                \A m \in 0..(N - 1) : proposed[m] <= v) => Liveness

====