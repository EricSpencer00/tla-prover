---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ T > 0 /\ 2 * T < N

States == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choose"}

MaxV == CHOOSE x \in Values : \A y \in Values : y <= x

VARIABLES loc, view, prop, est, decided, crashed, msgs, inbox

vars == <<loc, view, prop, est, decided, crashed, msgs, inbox>>

MsgTypes == {"p1", "p2"}

RECURSIVE MaxOf(_, _)
MaxOf(f, S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE IN LET y == MaxOf(f, S \ {x}) IN
       IF f[x] > y THEN f[x] ELSE y

TypeOK ==
  /\ loc \in [1..N -> States]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ msgs \subseteq [type : MsgTypes, val : Values, est : Values \cup {Bottom}, snd : 1..N]
  /\ inbox \in [1..N -> SUBSET (1..N)]

Init ==
  /\ loc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ inbox = [i \in 1..N |-> {}]

SendP1(i) ==
  /\ loc[i] = "b1"
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ msgs' = msgs \cup {[type |-> "p1", val |-> prop[i], est |-> Bottom, snd |-> i]}
  /\ UNCHANGED <<view, prop, est, decided, crashed, inbox>>

\* Phase-1 reception updates the local view only when the message type matches
\* the receiving process's current phase.
RecvP1(i, m) ==
  /\ loc[i] = "w1"
  /\ m.type = "p1"
  /\ m.snd \notin inbox[i]
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ inbox' = [inbox EXCEPT ![i] = inbox[i] \cup {m.snd}]
  /\ UNCHANGED <<loc, prop, est, decided, crashed, msgs>>

Prepare(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality(inbox[i]) >= N - T
  /\ est' = [est EXCEPT ![i] = MaxOf(view[i], 1..N)]
  /\ loc' = [loc EXCEPT ![i] = "prep"]
  /\ UNCHANGED <<view, prop, decided, crashed, msgs, inbox>>

SendP2(i) ==
  /\ loc[i] = "prep"
  /\ loc' = [loc EXCEPT ![i] = "b2"]
  /\ msgs' = msgs \cup {[type |-> "p2", val |-> prop[i], est |-> est[i], snd |-> i]}
  /\ UNCHANGED <<view, prop, est, decided, crashed, inbox>>

RecvP2(i, m) ==
  /\ loc[i] = "w2"
  /\ m.type = "p2"
  /\ m.snd \notin inbox[i]
  /\ view' = [view EXCEPT ![i][m.snd] = m.est]
  /\ inbox' = [inbox EXCEPT ![i] = inbox[i] \cup {m.snd}]
  /\ UNCHANGED <<loc, prop, est, decided, crashed, msgs>>

Decide(i) ==
  /\ loc[i] = "w2"
  /\ Cardinality({m \in (inbox[i] \cap {j \in 1..N : view[i][j] # Bottom}) :
       view[i][m] = est[i]}) >= N - T
  /\ decided' = [decided EXCEPT ![i] = est[i]]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, msgs, inbox>>

\* When the N-T threshold cannot be reached for any single estimate, the process
\* must still make progress by deterministically picking any known value.
Choose(i) ==
  /\ loc[i] = "w2"
  /\ inbox[i] = 1..N
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, msgs, inbox>>

CommitChoice(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values :
       /\ decided' = [decided EXCEPT ![i] = v]
       /\ view' = [view EXCEPT ![i] = [k \in 1..N |-> IF k = i THEN v ELSE view[i][k]]]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<prop, est, crashed, msgs, inbox>>

Crash(i) ==
  /\ loc[i] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decided, msgs, inbox>>

Next ==
  \/ \E i \in 1..N : SendP1(i) \/ SendP2(i) \/ Prepare(i) \/ Decide(i) \/ Choose(i) \/ CommitChoice(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in msgs : RecvP1(i, m) \/ RecvP2(i, m)

Fairness ==
  /\ \A i \in 1..N : WF_vars(SendP1(i))
  /\ \A i \in 1..N : WF_vars(\E m \in msgs : RecvP1(i, m))
  /\ \A i \in 1..N : SF_vars(Prepare(i))
  /\ \A i \in 1..N : WF_vars(SendP2(i))
  /\ \A i \in 1..N : WF_vars(\E m \in msgs : RecvP2(i, m))
  /\ \A i \in 1..N : SF_vars(Decide(i))
  /\ \A i \in 1..N : WF_vars(CommitChoice(i))
  /\ \A i \in 1..N : SF_vars(Crash(i))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

Validity ==
  \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : decided[i] = prop[j]

Agreement ==
  \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination ==
  \A i \in 1..N : (loc[i] \in {"done", "crashed"}) WF_vars(Next)

ConditionC1 ==
  (\A i \in 1..N : decided[i] = Bottom) =>
    (\E i \in 1..N : prop[i] = MaxV) =>
      (\E i \in 1..N : decided[i] # Bottom)

====