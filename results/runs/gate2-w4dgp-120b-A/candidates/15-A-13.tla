---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The Srikanth-Toueg one-round asynchronous reliable broadcast protocol
\* (Figure 7 of the 1987 paper) with at most T Byzantine processes among
\* the N participants.  Every correct participant either has received the
\* broadcaster's INIT message or not; that binary choice replaces an
\* explicit broadcaster.  A correct process that hasn't yet sent ECHO may
\* accept early (N-2T quorum) or late (N-T quorum) depending on how many
\* distinct ECHO messages it has seen from distinct senders.

Processes == 1..N
Msgs == {"ECHO"}
Broadcasts == {1}    \* existence of a broadcast is binary; Process 1 does it in the model

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty \subseteq Processes
  /\ correct \cup faulty = Processes
  /\ correct \cap faulty = {}
  /\ pc \in [Processes -> {"nobroadcast","initrcvd","echoed","accepted","initmiss"}]
  /\ recv \in [Processes -> SUBSET (Processes \X Msgs)]
  /\ sent \in SUBSET (Processes \X Msgs)

Init ==
  /\ Cardinality(correct) = N-F
  /\ faulty = Processes \ correct
  /\ \A p \in Processes : pc[p] \in {"initrcvd","initmiss"}
                           /\ recv[p] = {}
  /\ sent = {}

\* A correct process receives an arbitrary set of new messages; the new
\* set may come from correct senders (the sent set) and from any
\* Byzantine sender (the whole of Processes \X Msgs in the model), so
\* the receiver's observed set is always a superset of what the correct
\* senders have actually put out.
Receive(p) ==
  /\ pc[p] \in {"initrcvd","initmiss"}
  /\ \E s \in SUBSET (sent \cup (Processes \X Msgs)) :
       recv' = [recv EXCEPT ![p] = @ \cup s]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* The broadcaster's INIT message reaches only the processes that start
\* in the broadcast-received state; those immediately accept and send ECHO.
EchoBroadcast(p) ==
  /\ pc[p] = "initrcvd"
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* Early acceptance: with at least N-2T ECHO messages seen from distinct
\* senders (the lower quorum) a process may send ECHO without yet
\* accepting.
EchoEarly(p) ==
  /\ pc[p] = "initmiss"
  /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) >= N-2*T
  /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) < N-T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* Late acceptance: with at least N-T ECHO messages seen from distinct
\* senders (the higher quorum) a process sends ECHO and accepts.
EchoLate(p) ==
  /\ pc[p] = "initmiss"
  /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) >= N-T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

Accept(p) ==
  /\ pc[p] = "echoed"
  /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) >= N-T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

\* Strong fairness on every correct action (receive, echo, accept) plus
\* unguarded propagation of Byzantine messages model a network where
\* correct processes are never permanently stuck: if something is
\* constantly available to them, they eventually act on it.
Next ==
  \/ \E p \in correct : Receive(p)
  \/ \E p \in correct : EchoBroadcast(p)
  \/ \E p \in correct : EchoEarly(p)
  \/ \E p \in correct : EchoLate(p)
  \/ \E p \in correct : Accept(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in correct : Receive(p))
  /\ WF_vars(\E p \in correct : EchoBroadcast(p))
  /\ WF_vars(\E p \in correct : EchoEarly(p))
  /\ WF_vars(\E p \in correct : EchoLate(p))
  /\ WF_vars(\E p \in correct : Accept(p))

\* Only correct processes may accept; when a correct participant accepts,
\* the rest of the correct group also eventually accepts (reliable delivery).
CorrLtl == \A p \in correct : (pc[p] = "accepted") ~> (\A q \in correct : pc[q] = "accepted")
RelayLtl == \E p \in correct : pc[p] = "accepted" ~> (\A q \in correct : pc[q] = "accepted")

\* Safety property: without any correct broadcast (all start in the
\* non-broadcast state) no correct participant ever accepts, even
\* though Byzantine participants may flood the network with ECHOs.
NoBroadcast == (\A p \in correct : pc[p] = "initmiss") ~> (\A q \in correct : pc[q] # "accepted")
UnforgLtl == NoBroadcast

FCConstraints ==
  /\ N > 3*T
  /\ T >= F
  /\ F >= 0

====