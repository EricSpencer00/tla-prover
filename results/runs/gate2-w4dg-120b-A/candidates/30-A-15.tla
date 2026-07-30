---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  N, T, F, Values, Bottom

\* Phase: broadcast phase 1, waiting for phase 1, prepare, broadcast phase 2,
\* waiting for phase 2, done, crashed, or choosing.
Phases == {"p1b", "p1w", "prep", "p2b", "p2w", "done", "crashed", "choose"}

TypeOK ==
  /\ N \in Nat /\ T \in Nat /\ F \in Nat
  /\ Values \subseteq Nat /\ Bottom \in Nat
  /\ Cardinality(Values) >= 1
  /\ 2 * T < N
  /\ F <= T /\ N >= 1

VARIABLES phase, view, prop, est, decision, crashed, messages, rcvd

vars == <<phase, view, prop, est, decision, crashed, messages, rcvd>>

MsgTypes == {"p1", "p2"}
MaxInView(i) ==
  LET f[S \in SUBSET 1..N] ==
        IF S = {} THEN Bottom
        ELSE LET x == CHOOSE y \in S : TRUE
             IN IF view[i][x] > f[S \ {x}] THEN view[i][x] ELSE f[S \ {x}]
  IN f[1..N]

Init ==
  /\ phase = [i \in 1..N |-> "p1b"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [i \in 1..N |-> CHOOSE x \in Values : TRUE]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ messages = {}
  /\ rcvd = [i \in 1..N |-> {}]

BroadcastP1(i) ==
  /\ phase[i] = "p1b"
  /\ phase' = [phase EXCEPT ![i] = "p1w"]
  /\ messages' = messages \cup {[type |-> "p1", val |-> prop[i], from |-> i]}
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

ReceiveP1(i, m) ==
  /\ phase[i] = "p1w"
  /\ m \in messages
  /\ m.type = "p1"
  /\ i \notin rcvd[m.from]
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m.from}]
  /\ UNCHANGED <<phase, prop, est, decision, crashed, messages>>

P1ToP2(i) ==
  /\ phase[i] = "p1w"
  /\ Cardinality(rcvd[i]) >= N - T
  /\ est' = [est EXCEPT ![i] = MaxInView(i)]
  /\ phase' = [phase EXCEPT ![i] = "p2b"]
  /\ UNCHANGED <<view, prop, decision, crashed, messages, rcvd>>

BroadcastP2(i) ==
  /\ phase[i] = "p2b"
  /\ phase' = [phase EXCEPT ![i] = "p2w"]
  /\ messages' = messages \cup {[type |-> "p2", val |-> prop[i],
                     est |-> est[i], from |-> i]}
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

ReceiveP2(i, m) ==
  /\ phase[i] = "p2w"
  /\ m \in messages
  /\ m.type = "p2"
  /\ i \notin rcvd[m.from]
  /\ view' = [view EXCEPT ![i][m.from] = m.est]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m.from}]
  /\ UNCHANGED <<phase, prop, est, decision, crashed, messages>>

DecideP2(i) ==
  /\ phase[i] = "p2w"
  /\ \E val \in Values :
       /\ Cardinality({j \in 1..N : view[i][j] = val}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = val]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, messages, rcvd>>

Choose(i) ==
  /\ phase[i] = "p2w"
  /\ rcvd[i] = 1..N
  /\ phase' = [phase EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, messages, rcvd>>

DecideChoose(i) ==
  /\ phase[i] = "choose"
  /\ view[i][i] \in Values
  /\ decision' = [decision EXCEPT ![i] = view[i][i]]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, messages, rcvd>>

Crash(i) ==
  /\ crashed < F
  /\ phase[i] \notin {"done", "crashed"}
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, messages, rcvd>>

Next ==
  \/ \E i \in 1..N :
       \/ BroadcastP1(i) \/ P1ToP2(i) \/ BroadcastP2(i) \/ DecideP2(i)
       \/ Choose(i) \/ DecideChoose(i) \/ Crash(i)
       \/ \E m \in messages :
            \/ ReceiveP1(i, m) \/ ReceiveP2(i, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in messages : ReceiveP1(i, m))
  /\ WF_vars(\E i \in 1..N, m \in messages : ReceiveP2(i, m))
  /\ WF_vars(\E i \in 1..N : P1ToP2(i))
  /\ WF_vars(\E i \in 1..N : DecideP2(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))
  /\ WF_vars(\E i \in 1..N : DecideChoose(i))

Validity ==
  \A i \in 1..N : decision[i] # Bottom => decision[i] \in Values

Agreement ==
  \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom)
                     => decision[i] = decision[j]

Termination == <>(\A i \in 1..N : phase[i] \in {"done", "crashed"})

ConditionC1 ==
  \E S \subseteq 1..N :
    /\ Cardinality(S) >= F + 1
    /\ \A i \in S : prop[i] = Max(Values)
    /\ Termination

====