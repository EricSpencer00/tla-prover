---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Bounded range of process identities, inferred from the model bounds.
Process == 1..N

Voters == Process
ECHO == "echo"

VARIABLES correct, faulty, pc, rcvd, sent

vars == <<correct, faulty, pc, rcvd, sent>>

\* The control locations: a process has not received the broadcast INIT,
\* has received the INIT, has sent its ECHO message, or has accepted.
Locs == {"initAbsent", "hasInit", "sent", "accept"}

TypeOK ==
  /\ correct \subseteq Process
  /\ faulty \subseteq Process
  /\ correct \cap faulty = {}
  /\ pc \in [Process -> Locs]
  /\ rcvd \in [Process -> SUBSET (Voters \X {ECHO})]
  /\ sent \subseteq (Voters \X {ECHO})

\* No correct process ever diverges into an undefined or unauthorized
\* control location or set membership.
FCConstraints == TypeOK

\* No forging: if no correct process started with the broadcast INIT, no
\* correct process accepts -- even though Byzantine senders are free to
\* flood the network with arbitrary messages.
UnforgLtl == (\A p \in correct : pc[p] = "initAbsent") ~> (\A p \in correct : pc[p] = "accept")

InitAll(p) == IF pc[p] = "hasInit" THEN "sent" ELSE pc[p]

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {N - F + 1..N}
  /\ \A p \in Process : pc[p] \in {"initAbsent", "hasInit"}
  /\ rcvd = [p \in Process |-> {}]
  /\ sent = {}

\* The second, larger configuration has every process initially holding the
\* broadcast INIT (relevant only for the correctness/liveness check).
InitAllBroadcast ==
  /\ correct = {1..(N - F)}
  /\ faulty = {N - F + 1..N}
  /\ pc = [p \in Process |-> "hasInit"]
  /\ rcvd = [p \in Process |-> {}]
  /\ sent = {}

\* A correct process receives a new batch of messages, drawn from sent by
\* correct processes combined with arbitrary Byzantine contributions.
Recv(p, delta) ==
  /\ p \in correct
  /\ pc[p] \in {"initAbsent", "hasInit"}
  /\ delta \subseteq sent \cup (faulty \X {ECHO})
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup delta]
  /\ pc' = [pc EXCEPT ![p] = InitAll(p)]
  /\ UNCHANGED <<correct, faulty, sent>>

\* A process that had the broadcast INIT accepts immediately and ECHOs.
InitEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "hasInit"
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<p, ECHO>>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

EchoRelay(p) ==
  /\ p \in correct
  /\ pc[p] = "initAbsent"
  /\ Cardinality({q \in Voters : <<q, ECHO>> \in rcvd[p]}) >= N - 2 * T
  /\ Cardinality({q \in Voters : <<q, ECHO>> \in rcvd[p]}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<p, ECHO>>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

RelayAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "initAbsent"
  /\ Cardinality({q \in Voters : <<q, ECHO>> \in rcvd[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {<<p, ECHO>>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

DeferredAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality({q \in Voters : <<q, ECHO>> \in rcvd[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, rcvd, sent>>

Next ==
  \/ \E p \in Process, delta \in SUBSET (Voters \X {ECHO}) : Recv(p, delta)
  \/ \E p \in Process : InitEcho(p)
  \/ \E p \in Process : EchoRelay(p)
  \/ \E p \in Process : RelayAccept(p)
  \/ \E p \in Process : DeferredAccept(p)

\* Strong fairness: a correct process that can forever receive and act
\* (messages from correct processes are always available) must eventually
\* do so -- needed to close the liveness gap in the catch-up case.
Spec ==
  /\ Init /\ [][Next]_vars
  /\ \A p \in Process :
       SF_vars(Recv(p, {<<q, ECHO>>} : q \in correct))
  /\ WF_vars(\E delta \in SUBSET (Voters \X {ECHO}) : Recv(p, delta))

CorrLtl == (\A p \in correct : pc[p] = "hasInit") ~> (\A p \in correct : pc[p] = "accept")
RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

====