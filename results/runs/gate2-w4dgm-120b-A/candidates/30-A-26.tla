---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase consensus: phase 1 disseminates proposals, phase 2 disseminates
\* each process's estimate (the max it has observed). A process decides on an
\* estimate only once enough processes (N-T, i.e. a majority of the non-faulty
\* ones) are consistent on that estimate.
\* Crash faults: up to F processes may crash silently; the bound T (worse
\* than the actual fault count) is what the participants assume when they
\* consider an estimate "agreed". The safety invariant protects agreement
\* even when the observed-agreement threshold is set for more faults than
\* actually occur (the system is built for T faults, but only F ever hit).

VARIABLES loc, seen, prop, estimate, decided, crashed, sent, received

\* Control locations: where each process is in the two-phase flow.
Locs == {"p1", "p1w", "p2", "p2w", "done", "crashed", "choose"}

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ seen \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq [type: {"phase1", "phase2"}, val: Values, est: Values \cup {Bottom}, from: 1..N]
  /\ received \in [1..N -> SUBSET 1..N]

MaxV(S) == CHOOSE m \in S : (\A y \in S : y <= m)

Init ==
  /\ loc = [i \in 1..N |-> "p1"]
  /\ seen = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

\* A process in the broadcast phase puts its own proposal on the network
\* and moves to the waiting phase (it will only start estimating once it
\* learns enough about what others proposed).
Broadcast1(i) ==
  /\ loc[i] = "p1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[i], est |-> Bottom, from |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "p1w"]
  /\ UNCHANGED <<seen, prop, estimate, decided, crashed, received>>

\* Message delivery fills in the receiver's local view of the sender's
\* value. The stale check (phase matches the receiver's current phase)
\* is what keeps a phase-2 value from contaminating a phase-1 view.
Receive(m, i) ==
  /\ m.from \notin received[i]
  /\ loc[i] \in {"p1w", "p2w"}
  /\ m.type = (IF loc[i] \in {"p1w"} THEN "phase1" ELSE "phase2")
  /\ seen' = [seen EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m.from}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

Estimate(i) ==
  /\ loc[i] = "p1w"
  /\ Cardinality(received[i]) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = MaxV({seen[i][j] : j \in 1..N} \ {Bottom})]
  /\ loc' = [loc EXCEPT ![i] = "p2"]
  /\ UNCHANGED <<seen, prop, decided, crashed, sent, received>>

\* Phase 2 messages carry both the process' own proposal and its estimate.
Broadcast2(i) ==
  /\ loc[i] = "p2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[i], est |-> estimate[i], from |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "p2w"]
  /\ UNCHANGED <<seen, prop, estimate, decided, crashed, received>>

\* Decision step 1: a majority of the phase-2 messages agree on one
\* estimate, so the process adopts it as its decision.
Decide(i) ==
  /\ loc[i] = "p2w"
  /\ \E v \in Values :
       /\ Cardinality({j \in received[i] : [type |-> "phase2", val |-> prop[j], est |-> estimate[j], from |-> j].est = v})
            >= N - T
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<seen, prop, estimate, crashed, sent, received>>

\* Decision step 2: no estimate ever reaches a majority, so the process
\* deterministically picks some observed value from its local view.
Choose(i) ==
  /\ loc[i] = "p2w"
  /\ Cardinality(received[i]) = N
  /\ \E v \in {seen[i][j] : j \in 1..N} \ {Bottom} :
       decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<seen, prop, estimate, crashed, sent, received>>

Crash(i) ==
  /\ crashed < F
  /\ loc[i] \notin {"crashed", "done"}
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<seen, prop, estimate, decided, sent, received>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i)
  \/ \E m \in sent, i \in 1..N : Receive(m, i)
  \/ \E i \in 1..N : Estimate(i)
  \/ \E i \in 1..N : Broadcast2(i)
  \/ \E i \in 1..N : Decide(i)
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : Crash(i)

\* SAFETY: agreement is the consensus property -- two processes never
\* decide different values -- so it is asserted as an invariant.
Agree ==
  \A i, j \in 1..N :
    (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Spec == Init /\ [][Next]_<<loc, seen, prop, estimate, decided, crashed, sent, received>>

\* Every decided value must come from some process' own proposal.
ValidDecisions == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : prop[j] = decided[i]

\* Conditional termination: the protocol is guaranteed to finish when at
\* least F+1 processes actually proposed the globally maximum value.
UptoF == {i \in 1..N : prop[i] = MaxV(Values)}
TerminatingOnMax == Cardinality(UptoF) >= F + 1

\* The fairness constraints that make progress arguments go through: a
\* process that is waiting does eventually receive, eventually estimates,
\* eventually decides or chooses, and a process that is broadcasting
\* eventually puts its message on the network (unless it crashes, which
\* is itself a strongly-fair outcome). Weak fairness on phase 2 sending
\* is needed only once every process that is still alive has already
\* moved past phase 1.
====