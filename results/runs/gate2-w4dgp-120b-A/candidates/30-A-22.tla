---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ T <= N /\ 2 * T < N
       /\ F \in Nat /\ F <= T
       /\ Bottom \notin Values
       /\ Values # {}

VARIABLES loc, view, prop, estimate, decision, ncrash, sent, rcvd

vars == <<loc, view, prop, estimate, decision, ncrash, sent, rcvd>>

TypeOK ==
  /\ loc \in [1..N -> {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ ncrash \in 0..N
  /\ sent \subseteq (([1..N -> Values \cup {Bottom}] \times {"p1", "p2"}) \times (1..N))
  /\ rcvd \in [1..N -> SUBSET (1..N)]

Init ==
  /\ loc = [i \in 1..N |-> "bc1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ ncrash = 0
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]

Broadcast1(i) ==
  /\ loc[i] = "bc1"
  /\ sent' = sent \cup {([prop[i], "p1"], i)}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, estimate, decision, ncrash, rcvd>>

Receive1(i, j) ==
  /\ loc[i] = "w1"
  /\ (([prop[j], "p1"], j) \in sent)
  /\ j \notin rcvd[i]
  /\ view' = [view EXCEPT ![i][j] = prop[j]]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {j}]
  /\ UNCHANGED <<loc, prop, estimate, decision, ncrash, sent>>

Phase1Next(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality(rcvd[i]) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = {view[i][j] : j \in 1..N} \cap Values]
  /\ loc' = [loc EXCEPT ![i] = "bc2"]
  /\ UNCHANGED <<view, prop, decision, ncrash, sent, rcvd>>

Broadcast2(i) ==
  /\ loc[i] = "bc2"
  /\ sent' = sent \cup {(([prop[i], "p2"], estimate[i]), i)}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, estimate, decision, ncrash, rcvd>>

Receive2(i, j) ==
  /\ loc[i] = "w2"
  /\ (([prop[j], "p2"], estimate[j]), j) \in sent
  /\ j \notin rcvd[i]
  /\ view' = [view EXCEPT ![i][j] = estimate[j]]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {j}]
  /\ UNCHANGED <<loc, prop, estimate, decision, ncrash, sent>>

Decide(i, v) ==
  /\ loc[i] = "w2"
  /\ Cardinality({j \in rcvd[i] : view[i][j] = v}) >= N - T
  /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, ncrash, sent, rcvd>>

Choosing(i) ==
  /\ loc[i] = "w2"
  /\ rcvd[i] = 1..N
  /\ Cardinality({v \in Values : \E j \in 1..N : view[i][j] = v}) >= N - T
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, decision, ncrash, sent, rcvd>>

ChooseDet(i, v) ==
  /\ loc[i] = "choosing"
  /\ v \in {view[i][j] : j \in 1..N}
  /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, ncrash, sent, rcvd>>

Crash(i) ==
  /\ loc[i] \in {"bc1", "w1", "bc2", "w2"}
  /\ ncrash < F
  /\ ncrash' = ncrash + 1
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<view, prop, estimate, decision, sent, rcvd>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i)
  \/ \E i \in 1..N, j \in 1..N : Receive1(i, j)
  \/ \E i \in 1..N : Phase1Next(i)
  \/ \E i \in 1..N : Broadcast2(i)
  \/ \E i \in 1..N, j \in 1..N : Receive2(i, j)
  \/ \E i \in 1..N, v \in Values : Decide(i, v)
  \/ \E i \in 1..N : Choosing(i)
  \/ \E i \in 1..N, v \in Values : ChooseDet(i, v)
  \/ \E i \in 1..N : Crash(i)

Spec == Init /\ [][Next]_vars
          /\ WF_vars(\E i \in 1..N : Broadcast1(i))
          /\ WF_vars(\E i \in 1..N : Broadcast2(i))
          /\ WF_vars(\E i \in 1..N, j \in 1..N : Receive1(i, j))
          /\ WF_vars(\E i \in 1..N, j \in 1..N : Receive2(i, j))
          /\ WF_vars(\E i \in 1..N : Phase1Next(i))
          /\ WF_vars(\E i \in 1..N, v \in Values : Decide(i, v))
          /\ WF_vars(\E i \in 1..N : Choosing(i))
          /\ WF_vars(\E i \in 1..N, v \in Values : ChooseDet(i, v))

Validity == \A i \in 1..N : decision[i] # Bottom => decision[i] \in Values

Agreement == \A i, j \in 1..N :
               (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Terminate == \A i \in 1..N : (loc[i] = "crashed" \/ decision[i] # Bottom) ~> TRUE

CondTerminate == (\A i \in 1..N : decision[i] = Bottom)
                    ~> (\A i \in 1..N : decision[i] # Bottom)

Properties == Terminate /\ CondTerminate

====