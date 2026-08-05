---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A condition-based max-value consensus protocol (Figure 1, C1 from Mostefaoui et
\* al. 2003). The system is asynchronous with crash faults, modeled by the
\* nondeterministic Receive action (each receive of a queued message is a separate
\* step, which is exactly the weak fairness assumption the paper's two-phase
\* argument needs to hold under). The Reachable set is the full reachable-state
\* set, and the properties below are the lightweight correctness requirements the
\* reference config expects (validity/assignment and agreement).
ASSUME N \in Nat /\ N > 0
ASSUME T \in Nat /\ T > 0 /\ 2 * T < N
ASSUME F \in Nat /\ F <= T
ASSUME Bottom \notin Values

Locations == {"p1", "p2", "p3", "p4", "p5"}
Msgs == {"m1", "m2", "m3"}
Phases == {"phase1", "phase2"}
Vars == {"prop","est","dec","rnd","loc","view","sent","rcvd","crashed"}

MaxV(S) == CHOOSE x \in S : (\A y \in S : y <= x)

TypeOK ==
  /\ loc \in [Locations -> {"broadcast1","wait1","prepare","broadcast2","wait2","done","crashed","choose"}]
  /\ view \in [Locations -> [Locations -> Values \cup {Bottom}]]
  /\ est \in [Locations -> Values \cup {Bottom}]
  /\ dec \in [Locations -> Values \cup {Bottom}]
  /\ rnd \in [Vars -> Vars \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ rcvd \subseteq [Msgs -> [phase:Phases \cup {Bottom}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: Locations \cup {Bottom}]]

Init ==
  /\ \E p \in Locations : loc = [q \in Locations |-> IF q = p THEN "broadcast1" ELSE "broadcast1"]
  /\ \E p \in Locations : prop = [q \in Locations |-> IF q = p THEN IF p \in {"p1","p2"} THEN CHOOSE x \in Values : TRUE ELSE CHOOSE x \in Values : x # (CHOOSE y \in Values : TRUE) ELSE CHOOSE x \in Values : x]
  /\ view = [p \in Locations |-> [q \in Locations |-> Bottom]]
  /\ est = [p \in Locations |-> Bottom]
  /\ dec = [p \in Locations |-> Bottom]
  /\ rnd = [v \in Vars |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = {}

Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ \E m \in Msgs \ sent :
       loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, est, dec, sent, rcvd, rnd, crashed>>

Receive1(p, m) ==
  /\ loc[p] \in {"wait1","prepare"}
  /\ m \notin sent
  /\ loc[p] = "wait1"
  /\ rcvd' = rcvd \cup {[m] = [phase |-> "phase1", val |-> propp, est |-> Bottom, from |-> pr] : pr \in Locations /\ propp \in Values}
  /\ sent' = sent \cup {m}
  /\ view' = [view EXCEPT ![p] = [q \in view[p] : IF q = pr THEN propp ELSE view[p][q]]]
  /\ UNCHANGED <<loc, est, dec, rnd, crashed>>

Compute(p) ==
  /\ loc[p] = "wait1"
  /\ (Cardinality({q \in Locations : view[p][q] # Bottom}) + crashed) >= (N - T)
  /\ est' = [est EXCEPT ![p] = MaxV({view[p][q] : q \in Locations /\ view[p][q] # Bottom})]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ rnd' = [rnd EXCEPT !["est"] = "est"]
  /\ UNCHANGED <<view, dec, sent, rcvd, crashed>>

Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ \E m \in Msgs \ sent :
       loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, est, dec, sent, rcvd, rnd, crashed>>

Receive2(p, m) ==
  /\ loc[p] \in {"wait2","prepare"}
  /\ m \notin sent
  /\ loc[p] = "wait2"
  /\ rcvd' = rcvd \cup {[m] = [phase |-> "phase2", val |-> propp, est |-> estp, from |-> pr] : pr \in Locations /\ propp \in Values /\ estp \in Values}
  /\ sent' = sent \cup {m}
  /\ view' = [view EXCEPT ![p] = [q \in view[p] : IF q = pr THEN estp ELSE view[p][q]]]
  /\ UNCHANGED <<loc, est, dec, rnd, crashed>>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({q \in Locations : \E m \in rcvd : m.from = q /\ m.phase = "phase2" /\ m.est = est[p]}) >= (N - T)
  /\ dec' = [dec EXCEPT ![p] = est[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ rnd' = [rnd EXCEPT !["dec"] = "dec"]
  /\ UNCHANGED <<view, est, sent, rcvd, crashed>>

Choose(p) ==
  /\ loc[p] = "wait2"
  /\ \A q \in Locations : \E m \in rcvd : m.from = q /\ m.phase = "phase2"
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ rnd' = [rnd EXCEPT !["choose"] = "choose"]
  /\ UNCHANGED <<view, est, dec, sent, rcvd, crashed>>

Final(p) ==
  /\ loc[p] \in {"choose","wait2"}
  /\ view[p][p] # Bottom
  /\ dec' = [dec EXCEPT ![p] = view[p][p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ rnd' = [rnd EXCEPT !["final"] = "final"]
  /\ UNCHANGED <<view, est, sent, rcvd, crashed>>

Crash(p) ==
  /\ loc[p] \notin {"done","crashed"}
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, est, dec, sent, rcvd, rnd>>

Next ==
  \/ \E p \in Locations : Broadcast1(p) \/ Compute(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ Final(p) \/ Crash(p)
  \/ \E p \in Locations, m \in Msgs : Receive1(p, m) \/ Receive2(p, m)

Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, est, dec, rnd, sent, rcvd, crashed>>
  /\ WF_vars(Next)
  /\ WF_vars(Crash("p1"))

Validity == \A p \in Locations : dec[p] # Bottom => \E q \in Locations : prop[q] = dec[p]
Agreement == \A p, q \in Locations : (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]
Termination == <>(\A p \in Locations : loc[p] \in {"done","crashed"})
C1Termination ==
  <>(\E p \in Locations : prop[p] = MaxV(Values) /\ \A q \in Locations : loc[q] \in {"done","crashed"})

====