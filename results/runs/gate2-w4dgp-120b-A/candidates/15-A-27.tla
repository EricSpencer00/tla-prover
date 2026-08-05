---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Two-state encoding instead of a dedicated broadcaster: a process that received the
\* broadcaster's INIT message starts already in the "broadcast state", which is what
\* triggers its immediate ECHO and eventual acceptance. Faulty processes are fixed by
\* the chosen Correct/Faulty partition and may send arbitrary messages.
\* Actions: Receive (a correct process gets any pending messages), Broadcast (an
\* init-received process accepts and ECHOs), Relay (an ECHO-receiving process that
\* has not yet sent ECHO does so once it has enough ECHOs but not enough to accept),
\* Strong (similar, but at the accept threshold), Accept (a process that already sent
\* ECHO accepts once it reaches the accept threshold).
\* Safety: Unforgeability (no accept without an initial broadcast); TypeOK (domains).
\* Liveness: CorrLtl (all correct accept when all correct broadcast); RelayLtl (acceptance propagates).
\* Fairness: weak fairness on the compound receive-and-act steps for each correct process.

VARIABLES loc, received, sent, correct

processes == 0..(N-1)
msgs == {"ECHO"}
sentBy == UNION {sent[p] : p \in processes}
NotSent == {p \in processes : sent[p] = {}}

TypeOK ==
  /\ loc \in [processes -> {"init", "noinit", "echoed", "accepted"}]
  /\ received \in [processes -> SUBSET (processes \X msgs)]
  /\ sent \in [processes -> SUBSET msgs]
  /\ correct \subseteq processes

FCConstraints == Cardinality(correct) = N-F

Init ==
  /\ loc \in [processes -> {"init", "noinit"}]
  /\ received = [p \in processes |-> {}]
  /\ sent = [p \in processes |-> {}]
  /\ correct \subseteq processes

InitNoBroadcast ==
  /\ loc \in [processes -> {"noinit"}]
  /\ received = [p \in processes |-> {}]
  /\ sent = [p \in processes |-> {}]
  /\ correct \subseteq processes

Receive(p) ==
  /\ p \in correct
  /\ received[p] # (received[p] \cup sentBy)
  /\ received' = [received EXCEPT ![p] = @ \cup sentBy]
  /\ UNCHANGED <<loc, sent, correct>>

Broadcast(p) ==
  /\ p \in correct
  /\ loc[p] = "init"
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sent' = [sent EXCEPT ![p] = @ \cup msgs]
  /\ UNCHANGED <<received, correct>>

Relay(p) ==
  /\ p \in correct
  /\ loc[p] \in {"init", "noinit"}
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in received[p]}) >= N - 2 * T
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in received[p]}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "echoed"]
  /\ sent' = [sent EXCEPT ![p] = @ \cup msgs]
  /\ UNCHANGED <<received, correct>>

Strong(p) ==
  /\ p \in correct
  /\ loc[p] \in {"init", "noinit"}
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in received[p]}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sent' = [sent EXCEPT ![p] = @ \cup msgs]
  /\ UNCHANGED <<received, correct>>

Accept(p) ==
  /\ p \in correct
  /\ loc[p] \in {"echoed"}
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in received[p]}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<received, sent, correct>>

Next ==
  \/ \E p \in processes : Receive(p)
  \/ \E p \in processes : Broadcast(p)
  \/ \E p \in processes : Relay(p)
  \/ \E p \in processes : Strong(p)
  \/ \E p \in processes : Accept(p)

Spec ==
  /\ Init /\ [][Next]_<<loc, received, sent, correct>>
  /\ \A p \in processes : WF_vars(Receive(p))
  /\ \A p \in processes : WF_vars(Broadcast(p))
  /\ \A p \in processes : WF_vars(Relay(p))
  /\ \A p \in processes : WF_vars(Stronger(p))
  /\ \A p \in processes : WF_vars(Accept(p))

SpecNoBroadcast ==
  /\ InitNoBroadcast /\ [][Next]_<<loc, received, sent, correct>>

UnforgLtl == (forall p \in processes : loc[p] = "init") ~> (forall p \in correct : loc[p] = "accepted")
CorrLtl == (forall p \in correct : loc[p] = "init") ~> (forall p \in correct : loc[p] = "accepted")
RelayLtl == (Exists p \in correct : loc[p] = "accepted") ~> (forall p \in correct : loc[p] = "accepted")

FAIRNESS == [typeOK -> TRUE, fcConstraints -> TRUE]

====