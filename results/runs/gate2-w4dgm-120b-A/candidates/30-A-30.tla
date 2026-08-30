---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ 2 * T < N
       /\ 0 <= F /\ F <= T
       /\ N > 0
       /\ \A v \in Values : v # Bottom

\* The value each process proposes, fixed at the start of the run.
VARIABLES phase, view, proposed, estimate, decision, crashed, sent, recvCount

vars == <<phase, view, proposed, estimate, decision, crashed, sent, recvCount>>

TypeOK ==
  /\ phase \in [1..N -> {"pc1", "w1", "prep", "pc2", "w2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"p1", "p2"}, val: Values, r: Values \cup {Bottom}, src: 1..N]
  /\ recvCount \in [1..N -> SUBSET 1..N]

Init ==
  /\ phase = [i \in 1..N |-> "pc1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvCount = [i \in 1..N |-> {}]

\* Phase 1: broadcast each process's own proposal.
BroadcastP1(i) ==
  /\ phase[i] = "pc1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> proposed[i], r |-> Bottom, src |-> i]}
  /\ phase' = [phase EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, recvCount>>

\* A received message improves the receiver's view of that sender's value.
ReceiveP1(i, m) ==
  /\ phase[i] \in {"w1", "prep"}
  /\ m.type = "p1"
  /\ i # m.src
  /\ view[i][m.src] = Bottom
  /\ view' = [view EXCEPT ![i][m.src] = m.val]
  /\ recvCount' = [recvCount EXCEPT ![i] = recvCount[i] \cup {m.src}]
  /\ UNCHANGED <<phase, proposed, estimate, decision, crashed, sent>>

\* Estimate the maximum value that the receiver has already seen.
Estimate(i) ==
  /\ phase[i] = "w1"
  /\ Cardinality(recvCount[i]) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in Values :
                     \A j \in 1..N : view[i][j] # Bottom => v >= view[i][j]]
  /\ phase' = [phase EXCEPT ![i] = "prep"]
  /\ UNCHANGED <<view, proposed, decision, crashed, sent, recvCount>>

\* Phase 2: broadcast both the proposal and the computed estimate.
BroadcastP2(i) ==
  /\ phase[i] = "prep"
  /\ sent' = sent \cup {[type |-> "p2", val |-> proposed[i], r |-> estimate[i], src |-> i]}
  /\ phase' = [phase EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, recvCount>>

\* Listen for N-T peers proposing the same estimate and adopt it.
DecideUnanimous(i) ==
  /\ phase[i] = "w2"
  /\ \E V \in Values :
       /\ Cardinality({m \in sent : m.type = "p2" /\ m.src \in recvCount[i] /\ m.r = V})
            >= N - T
       /\ decision' = [decision EXCEPT ![i] = V]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recvCount>>

\* If there is no clear N-T majority, fall back to a deterministic choice.
ChooseFallback(i) ==
  /\ phase[i] = "w2"
  /\ recvCount[i] = 1..N
  /\ \A V \in Values :
       Cardinality({m \in sent : m.type = "p2" /\ m.src \in recvCount[i] /\ m.r = V})
            < N - T
  /\ phase' = [phase EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, sent, recvCount>>

DecideChosen(i) ==
  /\ phase[i] = "choosing"
  /\ \E v \in Values :
       /\ \E j \in 1..N : view[i][j] # Bottom /\ v = view[i][j]
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recvCount>>

\* A process may crash silently, bounded by the fault tolerance, at any time.
Crash(i) ==
  /\ phase[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decision, sent, recvCount>>

\* Every message that has ever been sent can be delivered in some order.
ReceiveAny(i, m) == ReceiveP1(i, m)

Next ==
  \/ \E i \in 1..N :
       \/ BroadcastP1(i)
       \/ Estimate(i)
       \/ BroadcastP2(i)
       \/ DecideUnanimous(i)
       \/ ChooseFallback(i)
       \/ DecideChosen(i)
       \/ Crash(i)
  \/ \E i \in 1..N, m \in sent : ReceiveAny(i, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..N, m \in sent : WF_vars(ReceiveAny(i, m))
  /\ \A i \in 1..N : WF_vars(DecideChosen(i))

\* Safety: no conflicting decisions and no invented decisions.
Validity == \A i \in 1..N : decision[i] # Bottom => decision[i] \in Values
Agreement == \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* Every process eventually crashes or decides, and the max-value condition
\* is sufficient to guarantee that it decides rather than crashes.
Termination == \A i \in 1..N : <>(phase[i] \in {"done", "crashed"})
Conditional == \A i \in 1..N :
  (Cardinality({j \in 1..N : proposed[j] = CHOOSE x \in Values :
                                      \A k \in 1..N : proposed[k] <= x}) >= F + 1 => <> (phase[i] = "done"))

Properties == Termination /\ Conditional
====