---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

MessageTypes == {"phase1", "phase2"}

VARIABLES loc, view, prop, est, dec, crashedCount, sent, inbox

vars == <<loc, view, prop, est, dec, crashedCount, sent, inbox>>

Views == [1..N -> 1..N -> Values \cup {Bottom}]

\* loc: control location of each process;
\* view: each process's local view of every process's value (filled with Bottom);
\* prop: each process's proposed value; est: each process's estimated value after phase 1;
\* dec: each process's decision value; crashedCount: number of crashed processes;
\* sent: all sent messages; inbox: messages each process has received.
TypeOK ==
  /\ loc \in [1..N -> {"p1b","p1w","p2p","p2b","p2w","done","crashed","choosing"}]
  /\ view \in Views
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values]
  /\ dec \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..N
  /\ sent \subseteq [type : MessageTypes, val : Values, from : 1..N, est : Values \cup {Bottom}]
  /\ inbox \in [1..N -> SUBSET [type : MessageTypes, val : Values, from : 1..N, est : Values \cup {Bottom}]]

Init ==
  /\ loc = [p \in 1..N |-> "p1b"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ dec = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ inbox = [p \in 1..N |-> {}]

MaxOf(f) == CHOOSE x \in Values : \A y \in Values : y \in Range(f) => y <= x

\* Phase 1: broadcast proposed values.
BroadcastP1(p) ==
  /\ loc[p] = "p1b"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], from |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "p1w"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, inbox>>

ReceiveP1(p, m) ==
  /\ loc[p] = "p1w"
  /\ m.type = "phase1"
  /\ m \notin inbox[p]
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, sent>>

\* Compute the estimate once enough distinct messages are gathered.
TransitionP1(p) ==
  /\ loc[p] = "p1w"
  /\ Cardinality({m.from : m \in inbox[p] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxOf([q \in 1..N |-> view[p][q]])]
  /\ loc' = [loc EXCEPT ![p] = "p2b"]
  /\ UNCHANGED <<view, prop, dec, crashedCount, sent, inbox>>

\* Phase 2: broadcast own estimate.
BroadcastP2(p) ==
  /\ loc[p] = "p2b"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], from |-> p, est |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "p2w"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, inbox>>

ReceiveP2(p, m) ==
  /\ loc[p] = "p2w"
  /\ m.type = "phase2"
  /\ m \notin inbox[p]
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, sent>>

\* Decide on an estimate that reaches the N-T threshold.
DecideP2(p) ==
  /\ loc[p] = "p2w"
  /\ \E v \in Values :
        /\ Cardinality({m.from : m \in inbox[p] : m.type = "phase2" /\ m.est = v}) >= N - T
        /\ dec' = [dec EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, inbox>>

\* If no estimate reaches the threshold, choose a value from the view.
Choose(p) ==
  /\ loc[p] = "p2w"
  /\ \A v \in Values :
        Cardinality({m.from : m \in inbox[p] : m.type = "phase2" : m.est}) < N - T
  /\ \E v \in Values :
        /\ v \in Range([q \in 1..N |-> view[p][q]])
        /\ dec' = [dec EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, inbox>>

Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] \notin {"crashed","done"}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, inbox>>

Next ==
  \/ \E p \in 1..N : BroadcastP1(p) \/ BroadcastP2(p) \/ TransitionP1(p)
                     \/ DecideP2(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent : ReceiveP1(p, m) \/ ReceiveP2(p, m)

Spec == Init /\ [][Next]_vars
              /\ WF_vars(\E p \in 1..N, m \in sent : ReceiveP1(p, m))
              /\ WF_vars(\E p \in 1..N, m \in sent : ReceiveP2(p, m))
              /\ WF_vars(\E p \in 1..N : TransitionP1(p))
              /\ WF_vars(\E p \in 1..N : Choose(p))

Validity == \A p \in 1..N : dec[p] # Bottom => \E q \in 1..N : dec[p] = prop[q]

Agreement == \A p, q \in 1..N : (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done","crashed"})

C1 == Cardinality({p \in 1..N : prop[p] = MaxOf(prop)}) >= F + 1

ConditionalTermination == C1 ~> <>(\A p \in 1..N : loc[p] \in {"done","crashed"})

====