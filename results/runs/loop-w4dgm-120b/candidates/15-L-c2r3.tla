---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Accepted is a per-process flag, not a protocol action; it is set by
\* ReceiveEcho and Accept in the same step, never purely by a volatile
\* control-location change.
NoMsg == [frm |-> 0, typ |-> "none"]

VARIABLES correct, faulty, pc, rcvd, sent
vars == << correct, faulty, pc, rcvd, sent >>

Locations == {"init", "nobroadcast", "sent", "accepted"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> Locations]
  /\ rcvd \in [1..N -> SUBSET [frm : 1..N, typ : {"ECHO"}]]
  /\ sent \subseteq [frm : 1..N, typ : {"ECHO"}]

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {1..N} \ correct
  /\ pc \in [1..N -> {"init", "nobroadcast"}]
  /\ rcvd = [p \in 1..N |-> {}]
  /\ sent = {}

\* Restricted initial state: no correct process broadcast the message.
InitNoBroadcast ==
  /\ Init
  /\ \A p \in correct : pc[p] = "nobroadcast"

NewMessages(p) ==
  {m \in sent : (m. frm \in correct) /\ (m \notin rcvd[p])}
    \cup {[frm |-> q, typ |-> "ECHO"] : q \in faulty}

SendEcho(p) ==
  {m \in sent : m.frm \notin {p} /\ (m. frm \in correct)} \cup {[frm |-> p, typ |-> "ECHO"]}

DistinctSenders(S) == Cardinality({m.frm : m \in S})

\* A correct process receiving the INIT message immediately accepts it.
ReceiveInit(p) ==
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ rcvd' = [rcvd EXCEPT ![p] = SendEcho(p)]
  /\ sent' = SendEcho(p)
  /\ UNCHANGED << correct, faulty >>

\* Receiving messages is nondeterministic; a process can be slow but not failed.
ReceiveEcho(p) ==
  /\ pc[p] \in {"init", "nobroadcast"}
  /\ NewMessages(p) # {}
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup NewMessages(p)]
  /\ sent' = sent \cup SendEcho(p)
  /\ pc' = IF pc[p] = "init" \/ DistinctSenders(rcvd[p] \cup NewMessages(p)) >= (N - 2 * T)
            THEN "sent" ELSE pc[p]
  /\ UNCHANGED << correct, faulty >>

Accept(p) ==
  /\ pc[p] = "sent"
  /\ DistinctSenders(rcvd[p]) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, faulty, rcvd, sent >>

Next ==
  \/ \E p \in 1..N : ReceiveInit(p) \/ ReceiveEcho(p) \/ Accept(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in correct : SF_vars(ReceiveInit(p) \/ ReceiveEcho(p) \/ Accept(p))
  /\ \A p \in correct : WF_vars(\E q \in correct : ReceiveInit(q) \/ ReceiveEcho(q) \/ Accept(q))
  /\ \A p \in correct : WF_vars(ReceiveEcho(p))
  /\ \A p \in correct : WF_vars(Accept(p))

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")
UnforgLtl == (\A p \in correct : pc[p] = "nobroadcast") ~> (\A p \in correct : pc[p] # "accepted")
====