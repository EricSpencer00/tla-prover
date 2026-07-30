---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, rcvd, sent

vars == <<correct, faulty, loc, rcvd, sent>>
Msgs == [snd : 1..N, typ : {"ECHO"}]

RECURSIVE Reachable(_)
Reachable(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN {x} \cup Reachable(S \ {x})

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ loc \in [1..N -> {"init", "noinit", "sent", "done"}]
  /\ rcvd \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs

FCConstraints ==
  /\ \A p \in 1..N : (p \in correct) <=> ~(p \in faulty)
  /\ Cardinality(sent) <= N * (N - 1) + F * N
  /\ \A p \in 1..N : rcvd[p] \subseteq sent \cup Reachable(Msgs)

Init ==
  /\ correct \subseteq (1..N)
  /\ faulty = (1..N) \ correct
  /\ loc \in [1..N -> {"init", "noinit", "sent", "done"}]
  /\ rcvd = [p \in 1..N |-> {}]
  /\ sent = {}

Receive(p, S) ==
  /\ p \in correct
  /\ loc[p] \notin {"sent", "done"}
  /\ S \subseteq sent
  /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup S]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

RecvInit(p) ==
  /\ p \in correct
  /\ loc[p] = "init"
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rcvd>>

RecvQuorum(p) ==
  /\ p \in correct
  /\ loc[p] \notin {"sent", "done"}
  /\ Cardinality({m \in rcvd[p] : m.typ = "ECHO"}) >= N - 2 * T
  /\ Cardinality({m \in rcvd[p] : m.typ = "ECHO"}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rcvd>>

RecvAccept(p) ==
  /\ p \in correct
  /\ loc[p] \notin {"done"}
  /\ Cardinality({m \in rcvd[p] : m.typ = "ECHO"}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ sent' = sent \cup {[snd |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rcvd>>

AcceptOnly(p) ==
  /\ p \in correct
  /\ loc[p] = "sent"
  /\ Cardinality({m \in rcvd[p] : m.typ = "ECHO"}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<correct, faulty, rcvd, sent>>

Next ==
  \/ \E p \in 1..N, S \in SUBSET Msgs : Receive(p, S)
  \/ \E p \in 1..N : RecvInit(p)
  \/ \E p \in 1..N : RecvQuorum(p)
  \/ \E p \in 1..N : RecvAccept(p)
  \/ \E p \in 1..N : AcceptOnly(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, S \in SUBSET Msgs : Receive(p, S))
  /\ WF_vars(\E p \in 1..N : RecvQuorum(p))
  /\ WF_vars(\E p \in 1..N : RecvAccept(p))
  /\ WF_vars(\E p \in 1..N : AcceptOnly(p))

CorrLtl == <>(\A p \in correct : loc[p] = "done")
RelayLtl == (\E p \in correct : loc[p] = "done") ~> (\A p \in correct : loc[p] = "done")
UnforgLtl == (\A p \in correct : loc[p] = "noinit") ~> (\A p \in correct : loc[p] # "done")

====