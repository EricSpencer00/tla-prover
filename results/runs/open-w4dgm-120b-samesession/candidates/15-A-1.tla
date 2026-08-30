---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* Model: a one-round Byzantine-resilient broadcast.  `loc` is the control
\* location per process; `rcvd` the set of messages a process has seen.
\* Correct processes start either already having received the broadcaster's
\* INIT message or not.
\* Safety: Unforgeability (no accept without a genuine broadcast).
\* Liveness: CorrLtl (all accept if INIT was broadcast), RelayLtl (acceptance
\* propagates).  Variables are bounded to keep the reachable state space small.

Nodes == 1..N
Msgs == [snd: Nodes, typ: {"ECHO"}]

VARIABLES correct, faulty, loc, rcvd, sentAny
vars == <<correct, faulty, loc, rcvd, sentAny>>

InitLoc == "initstate"    \* INIT received or not (a runtime input, not a message)
\* States: initstate, initrcv, echoSent, accept.
Locs == {"initstate", "initrcv", "echoSent", "accept"}
Senders(m) == {x \in Nodes : [snd |-> x, typ |-> "ECHO"] \in m}

InitSpace == {1..N} \ {F}
\* The "no broadcast" subspace: nobody receives the broadcaster's INIT.
NoBroad == [n \in Nodes |-> IF n \in InitSpace THEN "initstate" ELSE "initrcv"]

TypeOK ==
  /\ correct \subseteq Nodes
  /\ faulty = Nodes \ correct
  /\ loc \in [Nodes -> Locs]
  /\ rcvd \in [Nodes -> SUBSET Msgs]
  /\ sentAny \subseteq Nodes

\* Unforgeability: with nobody genuinely broadcasting, nobody accepts.
FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = Nodes

Init ==
  /\ correct = InitSpace
  /\ faulty = Nodes \ correct
  /\ loc \in {NoBroad, [n \in Nodes |-> "initrcv"]}
  /\ rcvd = [n \in Nodes |-> {}]
  /\ sentAny = {}

AnyMsg(n) == CHOOSE m \in rcvd[n] : TRUE

\* A correct node may absorb any set of fresh messages, including Byzantine ones.
Receive(n, mset) ==
  /\ n \in correct
  /\ loc[n] \notin {"echoSent", "accept"}
  /\ mset \subseteq sentAny \cup { [snd |-> f, typ |-> "ECHO"] : f \in faulty }
  /\ rcvd' = [rcvd EXCEPT ![n] = mset]
  /\ UNCHANGED <<correct, faulty, loc, sentAny>>

\* A node that had the INIT message accepts immediately and sends its ECHO.
AcceptInit(n) ==
  /\ n \in correct
  /\ loc[n] = "initrcv"
  /\ loc' = [loc EXCEPT ![n] = "accept"]
  /\ sentAny' = sentAny \cup {n}
  /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {AnyMsg(n)}]
  /\ UNCHANGED <<correct, faulty>>

RelayEmit(n) ==
  /\ n \in correct
  /\ loc[n] = "initstate"
  /\ (N - 2 * T) <= Cardinality(Senders(rcvd[n]))
  /\ Cardinality(Senders(rcvd[n])) < (N - T)
  /\ loc' = [loc EXCEPT ![n] = "echoSent"]
  /\ sentAny' = sentAny \cup {n}
  /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {AnyMsg(n)}]
  /\ UNCHANGED <<correct, faulty>>

AcceptEmit(n) ==
  /\ n \in correct
  /\ loc[n] \in {"initstate", "echoSent"}
  /\ (N - T) <= Cardinality(Senders(rcvd[n]))
  /\ loc' = [loc EXCEPT ![n] = "accept"]
  /\ sentAny' = sentAny \cup {n}
  /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {AnyMsg(n)}]
  /\ UNCHANGED <<correct, faulty>>

RelayAccept(n) ==
  /\ n \in correct
  /\ loc[n] = "echoSent"
  /\ (N - T) <= Cardinality(Senders(rcvd[n]))
  /\ loc' = [loc EXCEPT ![n] = "accept"]
  /\ UNCHANGED <<correct, faulty, rcvd, sentAny>>

Next ==
  \/ \E n \in Nodes, mset \in SUBSET Msgs : Receive(n, mset)
  \/ \E n \in Nodes : AcceptInit(n) \/ RelayEmit(n) \/ AcceptEmit(n) \/ RelayAccept(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Nodes, mset \in SUBSET Msgs : Receive(n, mset))
  /\ WF_vars(\E n \in Nodes : AcceptInit(n))
  /\ WF_vars(\E n \in Nodes : RelayEmit(n))
  /\ WF_vars(\E n \in Nodes : AcceptEmit(n))
  /\ WF_vars(\E n \in Nodes : RelayAccept(n))

CorrLtl == (loc[1] = "initrcv") ~> (\A n \in correct : loc[n] = "accept")
RelayLtl == (\E n \in correct : loc[n] = "accept") ~> (\A n \in correct : loc[n] = "accept")
UnforgLtl == (\A n \in correct : loc[n] # "initrcv") ~> (\A n \in correct : loc[n] # "accept")
====