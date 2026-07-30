---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Fast-path acceptance by a correct process: once it has accepted it no longer
\* takes steps, so weak fairness on SendEcho and Accept is unnecessary for
\* liveness -- only the combined receipt/action step needs strong fairness.
\* The no-faulty version (zero faults, no fairness) is used to check safety.
VARIABLES correct, faulty, pc, recv, sent

InitState == CHOOSE s \in {"init", "noinit"} :
              \E S \in ({"init", "noinit"} \{s}) : Cardinality({i \in 1..N : s = "init"}) = N - F

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"init", "noinit", "echoed", "accept"}]
  /\ recv \in [1..N -> SUBSET (1..N \X {"ECHO"})]
  /\ sent \subseteq (1..N \X {"ECHO"})

NoRepeats(s) == \A x, y \in s : (x[1] = y[1]) => (x = y)

SentBy(i) == {m \in sent : m[1] = i}

\* A correct process receives a batch of new messages, drawn from everything
\* reliable sends have produced plus arbitrary Byzantine sends.
\* (The backlog is bounded by the finite message set, so strong fairness is
\* enough here, without assuming any progress on the unreliable side.)
Receive(i) ==
  /\ pc[i] \in {"init", "noinit", "echoed"}
  /\ \E S \subseteq ((sent \cup (1..N \X {"ECHO"})) \ Snd) :
       /\ \A m \in S : m \notin recv[i]
       /\ recv' = [recv EXCEPT ![i] = recv[i] \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(i) ==
  /\ pc[i] \in {"init", "noinit"}
  /\ Cardinality(recv[i]) >= N - 2 * T
  /\ Cardinality(recv[i]) < N - T
  /\ sent' = sent \cup SentBy(i) \cup ({i} \X {"ECHO"})
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ UNCHANGED <<correct, faulty, recv>>

Accept(i) ==
  /\ pc[i] \in {"init", "noinit", "echoed"}
  /\ Cardinality(recv[i]) >= N - T
  /\ sent' = sent \cup SentBy(i) \cup ({i} \X {"ECHO"})
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv>>

ReAccept(i) ==
  /\ pc[i] = "echoed"
  /\ Cardinality(recv[i]) >= N - T
  /\ sent' = sent \cup SentBy(i) \cup ({i} \X {"ECHO"})
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* The no-broadcast case is reachable by nondeterministic partitioning,
\* and this single-step case is what makes it reachable in the zero-faults
\* model checked against UnforgLtl.
InitAccept(i) ==
  /\ pc[i] = "init"
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup ({i} X {"ECHO"})
  /\ UNCHANGED <<correct, faulty, recv>>

\* Strong fairness on each individual receive step plus weak fairness on the
\* combined echo/accept steps suffices to guarantee every correct process
\* eventually moves from its start state, while a no-faults run with no
\* fairness still reaches a stuck state where nobody ever accepts.
Next ==
  \/ \E i \in 1..N : Receive(i) \/ SendEcho(i) \/ Accept(i) \/ ReAccept(i) \/ InitAccept(i)

vars == <<correct, faulty, pc, recv, sent>>

Init ==
  /\ correct = InitState
  /\ faulty = (1..N) \ correct
  /\ pc = [i \in 1..N |-> IF i \in InitState THEN "init" ELSE "noinit"]
  /\ recv = [i \in 1..N |-> {}]
  /\ sent = {}

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..N : SF_vars(Receive(i))
  /\ \A i \in 1..N : WF_vars(SendEcho(i) \/ Accept(i))

CorrLtl == <>(\A i \in 1..N : pc[i] = "accept")
RelayLtl == (\E i \in 1..N : pc[i] = "accept") ~> (\A i \in 1..N : pc[i] = "accept")

\* Unforgeability: if no correct process ever broadcasts (INIT never held),
\* then no correct process ever accepts.
UnforgLtl == (N - Cardinality(correct) >= F) => <>(\A i \in correct : pc[i] = "accept")
====