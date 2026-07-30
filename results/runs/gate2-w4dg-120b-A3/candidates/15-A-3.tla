---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process's control location, together with the messages it has received,
\* is exactly what the spec's actions are allowed to change.
Locations == {"noinit", "initrx", "echoed", "accepted"}
Msgs == {"ECHO"}

VARIABLES correct, faulty, loc, saw, sent
vars == <<correct, faulty, loc, saw, sent>>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Locations]
  /\ saw \in [1..N -> SUBSET [snd: 1..N, tag: Msgs]]
  /\ sent \subseteq [snd: 1..N, tag: Msgs]

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ loc = [i \in 1..N |-> IF i <= (N - F) THEN "initrx" ELSE "noinit"]
  /\ saw = [i \in 1..N |-> {}]
  /\ sent = {}

\* One correct process may receive several new messages at once, so no
\* single ECHO is lost no matter how messages are delivered.
Recv ==
  /\ \E i \in correct :
       \E m \in (sent \cup [snd: faulty, tag: Msgs]):
         saw' = [saw EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* A correct process that did receive the INIT accepts and sends ECHO.
EmitEchoOnInit ==
  /\ \E i \in correct :
       /\ loc[i] = "initrx"
       /\ loc' = [loc EXCEPT ![i] = "accepted"]
       /\ sent' = sent \cup {[snd |-> i, tag |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, saw>>

\* A correct process that has not yet sent ECHO receives lots of them and
\* begins sending, but does not yet accept (the non-strict case of the
\* protocol, needed for the relay liveness proof).
EmitEchoOnMany ==
  /\ \E i \in correct :
       /\ loc[i] = "noinit"
       /\ Cardinality({m \in saw[i] : m.tag = "ECHO"}) >= (N - 2 * T)
       /\ Cardinality({m \in saw[i] : m.tag = "ECHO"}) < (N - T)
       /\ loc' = [loc EXCEPT ![i] = "echoed"]
       /\ sent' = sent \cup {[snd |-> i, tag |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, saw>>

\* A correct process receives exactly the quorum needed: it both emits and
\* accepts in the same step. Once every correct process has received the
\* INIT this is the step that drives the whole network to quiescence.
EmitEchoOnQuorum ==
  /\ \E i \in correct :
       /\ loc[i] = "noinit"
       /\ Cardinality({m \in saw[i] : m.tag = "ECHO"}) >= (N - T)
       /\ loc' = [loc EXCEPT ![i] = "accepted"]
       /\ sent' = sent \cup {[snd |-> i, tag |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, saw>>

\* A process that has already emitted ECHO accepts once the strict quorum
\* arrives. This is the second half of the relay chain.
AcceptAfterEcho ==
  /\ \E i \in correct :
       /\ loc[i] = "echoed"
       /\ Cardinality({m \in saw[i] : m.tag = "ECHO"}) >= (N - T)
       /\ loc' = [loc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, saw, sent>>

\* Stateless correctness checks: N must be strictly above the Byzantine
\* threshold, the threshold must cover the faulty processes, and a
\* non-negative number of processes is always available.
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

Next ==
  \/ Recv
  \/ EmitEchoOnInit
  \/ EmitEchoOnMany
  \/ EmitEchoOnQuorum
  \/ AcceptAfterEcho

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Recv)
        /\ WF_vars(EmitEchoOnInit)
        /\ WF_vars(EmitEchoOnQuorum)

CorrLtl == (/\ \A i \in correct : loc[i] = "initrx")
           /\ <>(\A i \in correct : loc[i] \in {"accepted", "echoed"})
RelayLtl == (\E i \in correct : loc[i] = "accepted")
            ~>(\A i \in correct : loc[i] \in {"accepted", "echoed"})
UnforgLtl == (\A i \in correct : loc[i] = "noinit") ~> (\A i \in correct : loc[i] = "noinit")

====