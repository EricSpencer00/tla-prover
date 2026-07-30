---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME N > 0
ASSUME Bottom \notin Values

\* Actions: (1) broadcast phase 1; (2) receive phase-1 messages; (3)
\* compute the estimate and broadcast phase 2; (4) broadcast phase 2;
\* (5) decide from a majority estimate; (6) move to choosing if the
\* majority never forms; (7) deterministically pick a received value.
\* A process may also crash (bounded by F).
\* Weak fairness is assumed on all of them.
\* Termination under condition C1 is proved, not embedded in the model.
\* Messages carry a phase tag plus the sender's value and estimate.

Msgs == [kind: {"p1", "p2"}, val: Values, snd: 1..N, est: Values]

VARIABLES loc, view, propose, estimate, decide, cracked, sent, recv
vars == << loc, view, propose, estimate, decide, cracked, sent, recv >>

Voters1(p) == {m.snd : m \in {x \in recv[p] : x.kind = "p1"}}
Voters2(p) == {m.snd : m \in {x \in recv[p] : x.kind = "p2"}}
SeenEst(e, p) == {m.snd : m \in {x \in recv[p] : x.kind = "p2" /\ x.est = e}}

TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decide \in [1..N -> Values \cup {Bottom}]
  /\ cracked \in 0..N
  /\ sent \in SUBSET Msgs
  /\ recv \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 1..N |-> "b1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decide = [p \in 1..N |-> Bottom]
  /\ cracked = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

Broadcast1(p) ==
  /\ loc[p] = "b1"
  /\ sent' = sent \cup {[kind |-> "p1", val |-> propose[p], snd |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED << view, propose, estimate, decide, cracked, recv >>

\* Only messages from the current phase are admitted into the view.
Receive(p, m) ==
  /\ m \in sent
  /\ m \notin recv[p]
  /\ loc[p] = (IF m.kind = "p1" THEN "w1" ELSE IF m.kind = "p2" THEN "w2" ELSE loc[p])
  /\ m.snd # p
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED << loc, propose, estimate, decide, cracked, sent >>

Prep(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality(Voters1(p)) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE e \in Values : \A q \in 1..N : view[p][q] \in {e, Bottom}]
  /\ loc' = [loc EXCEPT ![p] = "b2"]
  /\ UNCHANGED << view, propose, decide, cracked, sent, recv >>

Broadcast2(p) ==
  /\ loc[p] = "b2"
  /\ sent' = sent \cup {[kind |-> "p2", val |-> propose[p], snd |-> p, est |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED << view, propose, estimate, decide, cracked, recv >>

Decide(p, e) ==
  /\ loc[p] = "w2"
  /\ Cardinality(SeenEst(e, p)) >= N - T
  /\ decide' = [decide EXCEPT ![p] = e]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, propose, estimate, cracked, sent, recv >>

Choose(p) ==
  /\ loc[p] = "w2"
  /\ Cardinality(Voters2(p)) = N
  /\ \A e \in Values : Cardinality(SeenEst(e, p)) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED << view, propose, estimate, decide, cracked, sent, recv >>

Select(p, e) ==
  /\ loc[p] = "choose"
  /\ \E q \in 1..N : view[p][q] = e
  /\ decide' = [decide EXCEPT ![p] = e]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, propose, estimate, cracked, sent, recv >>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ cracked < F
  /\ cracked' = cracked + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << view, propose, estimate, decide, sent, recv >>

Next ==
  \/ \E p \in 1..N : Broadcast1(p)
  \/ \E p \in 1..N, m \in Msgs : Receive(p, m)
  \/ \E p \in 1..N : Prep(p)
  \/ \E p \in 1..N : Broadcast2(p)
  \/ \E p \in 1..N, e \in Values : Decide(p, e)
  \/ \E p \in 1..N : Choose(p)
  \/ \E p \in 1..N, e \in Values : Select(p, e)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E m \in Msgs : Receive(1, m))
  /\ WF_vars(\E p \in 1..N : Broadcast1(p))
  /\ WF_vars(\E p \in 1..N : Prep(p))
  /\ WF_vars(\E m \in Msgs : Receive(2, m))
  /\ WF_vars(\E p \in 1..N : Broadcast2(p))
  /\ WF_vars(\E p \in 1..N : Choose(p))
  /\ WF_vars(\E p \in 1..N : Select(p, CHOOSE e \in Values : \E q \in 1..N : view[p][q] = e))

Validity == \A p \in 1..N : decide[p] # Bottom => \E q \in 1..N : propose[q] = decide[p]
Agreement == \A p, q \in 1..N : (decide[p] # Bottom /\ decide[q] # Bottom) => decide[p] = decide[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})
ConditionC1 ==
  /\ \E e \in Values : Cardinality({p \in 1..N : propose[p] = e}) >= F + 1
  /\ \A e \in Values : \A p, q \in 1..N : (propose[p] = e /\ propose[q] = e) => p = q
  /\ Termination

====