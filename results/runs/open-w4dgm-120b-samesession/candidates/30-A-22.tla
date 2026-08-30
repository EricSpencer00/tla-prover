---------------------------- MODULE cbc_max ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, estimate, decided, crashed, sent, recv

vars == <<loc, view, prop, estimate, decided, crashed, sent, recv>>

TypeOK ==
  /\ loc \in [1..N ->
        {"ph1b", "ph1w", "preparing", "ph2b", "ph2w", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq [type: 1..2, val: Values, snd: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET (1..N)]

Init ==
  /\ loc = [i \in 1..N |-> "ph1b"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

Ph1Broadcast(i) ==
  /\ loc[i] = "ph1b"
  /\ sent' = sent \cup {[type |-> 1, val |-> prop[i], snd |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "ph1w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Ph1Receive(i) ==
  /\ loc[i] = "ph1w"
  /\ \E m \in (sent \cap [type |-> 1, snd |-> rec]),
       rec \in 1..N :
        /\ m.val \notin {view[i][j] : j \in 1..N}
        /\ view' = [view EXCEPT ![i][m.snd] = m.val]
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.snd}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

Ph1ToPh2(i) ==
  /\ loc[i] = "ph1w"
  /\ Cardinality(recv[i]) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE mx \in Values :
                      \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= mx]
  /\ loc' = [loc EXCEPT ![i] = "ph2b"]
  /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

Ph2Broadcast(i) ==
  /\ loc[i] = "ph2b"
  /\ sent' = sent \cup {[type |-> 2, val |-> prop[i], snd |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "ph2w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Ph2Receive(i) ==
  /\ loc[i] = "ph2w"
  /\ \E m \in (sent \cap [type |-> 2, snd |-> rec]),
       rec \in 1..N :
        /\ \/ view[i][m.snd] = Bottom
           \/ \E g \in 1..N : view' = [view EXCEPT ![i][m.snd] = m.est]
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.snd}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

Ph2Decide(i) ==
  /\ loc[i] = "ph2w"
  /\ \E g \in Values :
       /\ (\A j \in 1..N : view[i][j] # Bottom => view[i][j] <= g)
       /\ (\A j \in 1..N : j \in recv[i] => view[i][j] = g)
       /\ decided' = [decided EXCEPT ![i] = g]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Ph2Choosing(i) ==
  /\ loc[i] = "ph2w"
  /\ recv[i] = 1..N
  /\ \A g \in Values :
       \E j \in 1..N : view[i][j] = g
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, sent, recv>>

Choose(i) ==
  /\ loc[i] = "choosing"
  /\ decided' = [decided EXCEPT ![i] = CHOOSE g \in view[i] : g # Bottom]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sent, recv>>

Next ==
  \E i \in 1..N :
    \/ Ph1Broadcast(i)
    \/ Ph1Receive(i)
    \/ Ph1ToPh2(i)
    \/ Ph2Broadcast(i)
    \/ Ph2Receive(i)
    \/ Ph2Decide(i)
    \/ Ph2Choosing(i)
    \/ Choose(i)
    \/ Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..N :
       /\ TRUE
       /\ WF_vars(Ph1Receive(i))
       /\ WF_vars(Ph1ToPh2(i))
       /\ WF_vars(Ph2Receive(i))
       /\ WF_vars(Ph2Decide(i))
       /\ WF_vars(Ph2Choosing(i))
       /\ WF_vars(Choose(i))

Validity ==
  \A i \in 1..N : decided[i] # Bottom => decided[i] \in {prop[j] : j \in 1..N}

Agreement ==
  \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination ==
  <>\E s \in [1..N -> {"crashed", "done"}] :
    \A i \in 1..N : loc[i] \in s[i]
=============================================================================