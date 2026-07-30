---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Control locations: no INIT, has INIT, sent ECHO, accepted.
Ctrls == {"noInit", "hasInit", "sentEcho", "accepted"}

\* Every process is either correct or faulty; at most T are faulty.
VARIABLES correct, faulty, pc, got, sent

vars == <<correct, faulty, pc, got, sent>>

Msgs == [fr : 1..N, tp : {"ECHO"}]
Unsent(p) == Cardinality({m \in sent : m.fr = p})

GotEchoes(p) == {m \in got[p] : m.tp = "ECHO"}
DistinctEchoSenders(p) == Cardinality({m \in GotEchoes(p) : m.fr})

InitSets == {"noInit", "hasInit"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> Ctrls]
  /\ got \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs

\* Weak fairness keeps correct processes receiving and acting.
\* A version without fairness is always available for safety-checking.
FCConstraints == FALSE

Init ==
  /\ correct = CHOOSE S \in SUBSET (1..N) : Cardinality(S) = N - F
  /\ faulty = (1..N) \ S
  /\ \E ss \in [1..N -> InitSets] :
        /\ pc = [p \in 1..N |-> ss[p]]
        /\ got = [p \in 1..N |-> {}]
  /\ sent = {}

InitNoBroadcast ==
  /\ correct = CHOOSE S \in SUBSET (1..N) : Cardinality(S) = N - F
  /\ faulty = (1..N) \ S
  /\ pc = [p \in 1..N |-> "noInit"]
  /\ got = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process receives new messages from correct and Byzantine senders.
Receive(p, new) ==
  /\ p \in correct
  /\ new \subseteq Msgs
  /\ new \cap got[p] = {}
  /\ got' = [got EXCEPT ![p] = got[p] \cup new]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"sentEcho", "accepted"}
  /\ sent' = sent \cup {[fr |-> p, tp |-> "ECHO"]}
  /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ UNCHANGED <<correct, faulty, got>>

\* A correct process that got the INIT message accepts and sends ECHO.
AcceptOnInit(p) ==
  /\ p \in correct
  /\ pc[p] = "hasInit"
  /\ SendEcho(p)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, got, sent>>

\* A correct process may send ECHO before it accepts.
SendEarly(p) ==
  /\ p \in correct
  /\ pc[p] = "noInit"
  /\ DistinctEchoSenders(p) >= (N - 2 * T)
  /\ DistinctEchoSenders(p) < (N - T)
  /\ SendEcho(p)
  /\ UNCHANGED <<correct, faulty, pc, got, sent>>

SendAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "noInit"
  /\ DistinctEchoSenders(p) >= (N - T)
  /\ SendEcho(p)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, got, sent>>

AcceptOnEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "sentEcho"
  /\ DistinctEchoSenders(p) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, got, sent>>

\* A correct process that already accepted may still receive messages.
Idle(p) ==
  /\ p \in correct
  /\ pc[p] = "accepted"
  /\ UNCHANGED vars

Next ==
  \/ \E p \in 1..N :
       \/ \E new \in SUBSET Msgs : Receive(p, new)
       \/ Idle(p) \/ AcceptOnInit(p) \/ SendEarly(p) \/ SendAndAccept(p) \/ AcceptOnEcho(p)

Spec ==
  /\ Init \/ InitNoBroadcast
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, new \in SUBSET Msgs : Receive(p, new))
  /\ WF_vars(\E p \in 1..N : SendEarly(p))
  /\ WF_vars(\E p \in 1..N : SendAndAccept(p))
  /\ WF_vars(\E p \in 1..N : AcceptOnEcho(p))

\* If no correct process ever broadcasts, none ever accepts.
UnforgLtl ==
  /\ \A p \in correct : pc[p] # "hasInit"
  /\ \A p \in correct : (pc[p] = "accepted") ~> (pc[p] = "noInit")

CorrLtl == (\A p \in correct : pc[p] = "hasInit") ~> (\A p \in correct : pc[p] = "accepted")

RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")

====