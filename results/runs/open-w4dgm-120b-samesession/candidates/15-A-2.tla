---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* A one-round async reliable broadcast with a bounded number of Byzantine
\* senders: a process may accept on N - 2T ECHOs, on N - T ECHOs, or on it
\* already being the broadcaster (the "emits INIT" case below).
\* Distinct-sender counting is what keeps an adversarial set of T faulty
\* processes from forcing a correct process to accept a forged broadcast.

\* pc[t] is a control location, not an FSM state, because a process can be
\* in the same location and still accept -- the ECHO-counting rules are
\* what separate those two cases, and they must be checked as separate
\* actions rather than a single "receive ECHOs" action.
Process == 1..N
Msg == [type : {"init", "echo"}, src : Process]

VARIABLES corr, faulty, pc, inbox, sent

TypeOK ==
  /\ corr \subseteq Process
  /\ faulty \subseteq Process
  /\ corr \cup faulty = Process
  /\ corr \cap faulty = {}
  /\ pc \in [Process -> {"startInit", "startNoInit", "sentEcho", "accepted"}]
  /\ inbox \in [Process -> SUBSET Msg]
  /\ sent \subseteq Msg

Init ==
  /\ corr = {i \in Process : i <= N - F}
  /\ faulty = Process \ corr
  /\ pc = [i \in Process |-> IF i <= N - F THEN "startInit" ELSE "startNoInit"]
  /\ inbox = [i \in Process |-> {}]
  /\ sent = {}

NoBroadcastInit ==
  /\ \A i \in Process : pc[i] = "startNoInit"
  /\ UNCHANGED <<corr, faulty, pc, inbox, sent>>

Receive(n, msgs) ==
  /\ n \in corr
  /\ msgs # {}
  /\ msgs \subseteq sent
  /\ inbox' = [inbox EXCEPT ![n] = inbox[n] \cup msgs]
  /\ UNCHANGED <<corr, faulty, pc, sent>>

\* A correct process that *did* receive the INIT message accepts immediately
\* and sends its own ECHO -- this is the one place the broadcaster matters.
EmitInit(n) ==
  /\ n \in corr
  /\ pc[n] = "startInit"
  /\ pc' = [pc EXCEPT ![n] = "accepted"]
  /\ sent' = sent \cup {[type |-> "echo", src |-> n]}
  /\ UNCHANGED <<corr, faulty, inbox>>

EmitEcho(n) ==
  /\ n \in corr
  /\ pc[n] \notin {"sentEcho", "accepted"}
  /\ Cardinality({m \in inbox[n] : m.type = "echo"}) >= N - 2 * T
  /\ Cardinality({m \in inbox[n] : m.type = "echo"}) < N - T
  /\ pc' = [pc EXCEPT ![n] = "sentEcho"]
  /\ sent' = sent \cup {[type |-> "echo", src |-> n]}
  /\ UNCHANGED <<corr, faulty, inbox>>

Accept(n) ==
  /\ n \in corr
  /\ pc[n] \notin {"sentEcho", "accepted"}
  /\ Cardinality({m \in inbox[n] : m.type = "echo"}) >= N - T
  /\ pc' = [pc EXCEPT ![n] = "accepted"]
  /\ sent' = sent \cup {[type |-> "echo", src |-> n]}
  /\ UNCHANGED <<corr, faulty, inbox>>

\* A process that has already sent its own ECHO may accept later without
\* sending another one -- this is the "acknowledge a completed broadcast"
\* branch of the spec and is what keeps an all-correct configuration from
\* being stuck when deliveries arrive out of order.
Acknowledge(n) ==
  /\ n \in corr
  /\ pc[n] = "sentEcho"
  /\ Cardinality({m \in inbox[n] : m.type = "echo"}) >= N - T
  /\ pc' = [pc EXCEPT ![n] = "accepted"]
  /\ UNCHANGED <<corr, faulty, inbox, sent>>

\* A Byzantine process can send whatever it wants; always available so no
\* correct process is ever stuck waiting for it, but its ECHOs are not
\* counted toward the acceptance thresholds.
ByzantineAction(n) ==
  /\ n \in faulty
  /\ sent' = sent \cup {[type |-> "echo", src |-> n]}
  /\ UNCHANGED <<corr, faulty, pc, inbox>>

Act ==
  \/ \E n \in Process : EmitInit(n)
  \/ \E n \in Process : EmitEcho(n)
  \/ \E n \in Process : Accept(n)

Next ==
  \/ Act
  \/ \E n \in Process : Receive(n, {m \in sent : m.src = n})
  \/ \E n \in Process : Acknowledge(n)
  \/ \E n \in Process : ByzantineAction(n)
  \/ NoBroadcastInit

Spec ==
  /\ Init
  /\ [][Next]_<<corr, faulty, pc, inbox, sent>>
  /\ WF_vars(Act)
  /\ SF_vars(\E n \in Process : EmitEcho(n))
  /\ SF_vars(\E n \in Process : Accept(n))

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

CorrLtl ==
  \A n \in corr :
    (pc[n] = "startInit") ~> (pc[n] = "accepted")

RelayLtl ==
  \A n \in corr : (pc[n] = "accepted") ~> (\A m \in corr : pc[m] = "accepted")

\* Unforgeability is a safety property derived from the distinct-sender
\* counting, so it has a separate proof obligation and does not need
\* strong fairness to hold in a model-checking run.
UnforgLtl ==
  (\A n \in corr : pc[n] = "startNoInit")
    => (\A n \in corr : pc[n] # "accepted")

====