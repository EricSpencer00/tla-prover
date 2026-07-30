---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Control locations: a process is in broadcast-received state, not-yet-received,
\* has sent an ECHO, or has accepted. `rcvd` names the message types each
\* process has actually observed; `sent` records what all correct processes
\* have broadcast so far, and is what the Byzantine processes complement.
Locs == {"initState", "noInit", "echoed", "accepted"}
Msgs == {"ECHO"}
NONE == "none"

VARIABLES correct, faulty, ctrl, rcvd, sent
vars == <<correct, faulty, ctrl, rcvd, sent>>

TypeOK ==
  /\ correct \subseteq (0..(N-1))
  /\ faulty \subseteq (0..(N-1))
  /\ ctrl \in [0..(N-1) -> Locs]
  /\ rcvd \in [0..(N-1) -> SUBSET Msgs]
  /\ sent \subseteq (0..(N-1))

\* The "no broadcast" case: every correct process starts without the INIT.
InitZero ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (0..(N-1)) \ correct
  /\ \A p \in 0..(N-1) : ctrl[p] = "noInit"
  /\ rcvd = [p \in 0..(N-1) |-> {}]
  /\ sent = {}

\* A richer start: some correct processes received the broadcaster's INIT.
InitFull ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (0..(N-1)) \ correct
  /\ \A p \in correct : ctrl[p] \in {"initState", "noInit"}
  /\ Cardinality({p \in correct : ctrl[p] = "initState"}) > 0
  /\ rcvd = [p \in 0..(N-1) |-> {}]
  /\ sent = {}

Init == InitZero \/ InitFull

RecvSome ==
  /\ \E p \in correct, S \subseteq (([msg : Msgs, from : 0..(N-1), snd : "C"] \cup
                                 [msg : Msgs, from : 0..(N-1), snd : "F"])) :
        /\ sent \subseteq S
                            /\ ctrl[p] \in {"initState", "noInit"}
                            /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup S]
  /\ UNCHANGED <<correct, faulty, ctrl, sent>>

SendsEcho(p) ==
  /\ ctrl[p] = "noInit"
  /\ ctrl' = [ctrl EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<correct, faulty, rcvd>>

AcceptsAfterN2T(p) ==
  /\ ctrl[p] = "noInit"
  /\ Cardinality({m \in rcvd[p] : m.msg = "ECHO"}) >= N - 2 * T
  /\ Cardinality({m \in rcvd[p] : m.msg = "ECHO"}) < N - T
  /\ ctrl' = [ctrl EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<correct, faulty, rcvd>>

AcceptsAfterNT(p) ==
  /\ ctrl[p] \in {"noInit", "echoed"}
  /\ Cardinality({m \in rcvd[p] : m.msg = "ECHO"}) >= N - T
  /\ ctrl' = [ctrl EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<correct, faulty, rcvd>>

Responses == \E p \in correct : SendsEcho(p) \/ AcceptsAfterN2T(p) \/ AcceptsAfterNT(p)

Next == Recur

CorrLtl == <>(\A p \in correct : ctrl[p] = "accepted")
RelayLtl == (<>(\E p \in correct : ctrl[p] = "accepted")) ~>
            (\A p \in correct : ctrl[p] = "accepted")
UnforgLtl == (\A p \in correct : ctrl[p] = "initState") ~> (\A p \in correct : ctrl[p] = "accepted")

\* Unforgeability holds without fairness (no broadcast case), while the
\* progress properties need strong fairness on the combined step.
Recur == RecurNoFair \/ RecurStrong
RecurNoFair == RecurStrong
RecurStrong == RecurStrong1
RecurStrong1 == (RecvSome \/ Responses) /\ UNCHANGED <<correct, faulty>>

\* Safety: no action ever lets a Byzantine process appear correct or a
\* correct process leave the correct set.
FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (0..(N-1)) \ correct

Spec == Init /\ [][Responses]_vars /\ WF_vars(Responses)

====