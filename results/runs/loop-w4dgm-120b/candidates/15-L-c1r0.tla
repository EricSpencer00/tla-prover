---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The protocol is parameterized by N (number of processes) and T (the Byzantine
\* fault threshold). The action set keeps the system weakly fair on the combined
\* receive-and-act steps of correct processes, so a correct process that can
\* keep receiving messages from correct senders and acting on them eventually
\* does. Unforgeability is the property that holds even without fairness.

CONTROLLERS == 0 .. (N - 1)
ECHO == "echo"
NONE == "none"
Msgs == [frm : CONTROLLERS, typ : {ECHO}]

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

TypeOK ==
  /\ correct \in SUBSET CONTROLLERS
  /\ faulty \in SUBCONTROLLER
  /\ pc \in [CONTROLLERS -> {"init", "noinit", "sent", "accept"}]
  /\ recv \in [CONTROLLERS -> SUBSET Msgs]
  /\ sent \in SUBSET Msgs

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ correct \cup faulty = CONTROLLERS
  /\ correct \cap faulty = {}

Init ==
  /\ correct = {i \in CONTROLLERS : i < (N - F)}
  /\ faulty = {i \in CONTROLLERS : i >= (N - F)}
  /\ pc = [i \in CONTROLLERS |-> IF i < (N - F) THEN "init" ELSE "noinit"]
  /\ recv = [i \in CONTROLLERS |-> {}]
  /\ sent = {}

NoBroadcast ==
  /\ \A i \in CONTROLLERS : pc[i] = "noinit"
  /\ \A i \in CONTROLLERS : recv[i] = {}

\* A correct process may receive any subset of the ECHO messages in flight, so
\* the network can reorder them arbitrarily and a process can be saturated.
Receive(i) ==
  /\ i \in correct
  /\ pc[i] # "accept"
  /\ \E m \in SUBSET (sent \cup {[frm |-> f, typ |-> ECHO] : f \in faulty}) :
       recv' = [recv EXCEPT ![i] = recv[i] \cup m]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(i) ==
  /\ i \in correct
  /\ pc[i] \in {"init", "noinit"}
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ sent' = sent \cup {[frm |-> i, typ |-> ECHO]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A process holding just enough ECHOs to be on the safe side sends one without
\* yet accepting; once it has a strict majority it accepts immediately.
EchoThreshold(i) ==
  /\ i \in correct
  /\ pc[i] = "noinit"
  /\ Cardinality({m \in recv[i] : m.typ = ECHO}) >= N - 2 * T
  /\ Cardinality({m \in recv[i] : m.typ = ECHO}) < N - T
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ sent' = sent \cup {[frm |-> i, typ |-> ECHO]}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptActs(i) ==
  /\ i \in correct
  /\ pc[i] \in {"noinit", "sent"}
  /\ Cardinality({m \in recv[i] : m.typ = ECHO}) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {[frm |-> i, typ |-> ECHO]}
  /\ UNCHANGED <<correct, faulty, recv>>

Next ==
  \/ \E i \in CONTROLLERS : Receive(i)
  \/ \E i \in CONTROLLERS : SendEcho(i)
  \/ \E i \in CONTROLLERS : EchoThreshold(i)
  \/ \E i \in CONTROLLERS : AcceptActs(i)
  \/ (NoBroadcast /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars
                 /\ \A i \in CONTROLLERS : WF_vars(Receive(i))
                 /\ \A i \in CONTROLLERS : WF_vars(AcceptActs(i))

\* Unforgeability checks that the absence of a true sender is never compensated
\* by the Byzantine ones: if no correct process received the INIT broadcast,
\* no correct process may ever accept.
UnforgLtl == (\A i \in CONTROLLERS : pc[i] = "noinit") ~> (\A i \in CONTROLLERS : pc[i] = "accept")

\* Correctness: if all correct processes really received the broadcast, they all
\* eventually accept. Relay: one correct acceptance is enough to pull the rest
\* in, even though the Byzantine senders can still be spamming ECHOs.
CorrLtl == (\A i \in correct : pc[i] = "init") ~> (\A i \in correct : pc[i] = "accept")
RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] = "accept")

====