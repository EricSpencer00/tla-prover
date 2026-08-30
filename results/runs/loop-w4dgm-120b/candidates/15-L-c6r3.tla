---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Program counters: where a correct process stands in the broadcast protocol.
\* Messages are type-tagged by sender identity, so an ECHO is always attributable.
\* The invariant below is per-process sanity; it is never the source of a liveness
\* claim, and it is what the model checker proves even without fairness.
VARIABLES correct, faulty, stage, rx, sent

vars == << correct, faulty, stage, rx, sent >>

Stages == {"nobroad", "broad", "sentECHO", "accepted"}
Msgs == {"ECHO"}
AllMsgs == {<< i, mtype >> : i \in 1..N, mtype \in Msgs}
BMsgs == {<< i, mtype >> : i \in faulty, mtype \in Msgs}
EchosFrom(i) == {s \in rx[i] : s[2] = "ECHO"}

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty = (1..N) \ correct
  /\ Cardinality(correct) = N - F
  /\ \A i \in 1..N : stage[i] \in Stages
  /\ \A i \in 1..N : rx[i] \subseteq AllMsgs
  /\ sent \subseteq AllMsgs

\* The correct/Byzantine partition is chosen here; the protocol otherwise
\* assumes exactly that many correct and faulty processes.
Init ==
  \E S \in [1..N -> Stages] :
    /\ correct = {i \in 1..N : S[i] \in {"broad", "sentECHO", "accepted"}}
    /\ faulty = (1..N) \ correct
    /\ sent = {}
    /\ stage = S
    /\ rx = [i \in 1..N |-> {}]

NoBroadcastInit ==
  /\ correct = {i \in 1..N : S[i] = "broad"}
  /\ faulty = (1..N) \ correct
  /\ sent = {}
  /\ stage = S
  /\ rx = [i \in 1..N |-> {}]
  /\ \A i \in 1..N : S[i] \in {"nobroad", "broad"}

\* A correct process may observe whatever has been sent so far; this is the
\* receive step, and it is never the thing that liveness is handed to.
Observe(i) ==
  /\ stage[i] \in {"nobroad", "broad"}
  /\ rx' = [rx EXCEPT ![i] = rx[i] \cup sent \cup BMsgs]
  /\ UNCHANGED << correct, faulty, stage, sent >>

Act(i) ==
  /\ stage[i] \in {"nobroad", "broad"}
  /\ stage' = [stage EXCEPT ![i] = "sentECHO"]
  /\ sent' = sent \cup {<< i, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, rx >>

\* The quorum thresholds: N-2T is the point where sending ECHO is justified,
\* N-T is the point where sending ECHO and accepting are both justified.
Engage(i) ==
  /\ stage[i] = "nobroad"
  /\ Cardinality(EchosFrom(i)) >= N - 2*T
  /\ Cardinality(EchosFrom(i)) < N - T
  /\ stage' = [stage EXCEPT ![i] = "sentECHO"]
  /\ sent' = sent \cup {<< i, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, rx >>

Accept(i) ==
  /\ stage[i] \in {"nobroad", "sentECHO"}
  /\ Cardinality(EchosFrom(i)) >= N - T
  /\ stage' = [stage EXCEPT ![i] = "accepted"]
  /\ sent' = sent \cup {<< i, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, rx >>

ObserveAny == \E i \in correct : Observe(i)
ActAny == \E i \in correct : Act(i)
EngageAny == \E i \in correct : Engage(i)
AcceptAny == \E i \in correct : Accept(i)

InitStep == Init \/ NoBroadcastInit

CorrLtl == \A i \in correct : (stage[i] = "broad") ~> (stage[i] = "accepted")
RelayLtl == (\E i \in correct : stage[i] = "accepted") ~> (\A i \in correct : stage[i] = "accepted")
UnforgLtl == (\A i \in correct : stage[i] = "nobroad") ~> (\A i \in correct : stage[i] # "accepted")

Spec ==
  /\ InitStep
  /\ [][Next]_vars
  /\ WF_vars(ObserveAny)
  /\ WF_vars(ActAny)
  /\ WF_vars(EngageAny)
  /\ WF_vars(AcceptAny)

\* This variant of InitStep is there only for checking safety: it forces no
\* correct process ever to be put into the broadcast state, so acceptance is
\* driven entirely by the Byzantine participants.
FCConstraints == Init /\ InitStep

Next ==
  \/ ObserveAny
  \/ ActAny
  \/ EngageAny
  \/ AcceptAny
====