---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Broadcast state: whether the one-round message was received.
\* Phi: the message type used throughout (an unforgeable tag).
Phi == "ECHO"

CorrectIds == 1..(N-F)
FaultyIds == ((N-F) + 1)..N

VARIABLES correct, faulty, prog, recvd, sent
vars == << correct, faulty, prog, recvd, sent >>

TypeOK ==
  /\ correct \subseteq (1..N) /\ Cardinality(correct) = N-F
  /\ faulty = (1..N) \ correct
  /\ prog \in [1..N -> {"idle", "noinit", "echoed", "accepted"}]
  /\ recvd \in [1..N -> SUBSET (1..N \X {Phi})]
  /\ sent \subseteq (1..N \X {Phi})

\* FCConstraints: no identifier ever leaves its domain; the count below is
\* exactly what the unforgeability proof hinges on.
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ \A q \in 1..N : prog[q] \in {"idle", "noinit", "echoed", "accepted"}

Init ==
  /\ correct = CorrectIds
  /\ faulty = FaultyIds
  /\ prog = [q \in 1..N |-> "idle"]
  /\ recvd = [q \in 1..N |-> {}]
  /\ sent = {}

\* The restricted initial state used for the no-broadcast case.
InitNoInit ==
  /\ Init
  /\ \A q \in correct : prog[q] = "noinit"

\* A correct process receives whatever it can (correct + Byzantine).
ReceiveMsgs(p) ==
  /\ p \in correct
  /\ \E M \in SUBSET (((1..N) \X {Phi}) \cup
        {m \in ((1..N) \X {Phi}) : m[1] \in faulty}) :
       recvd' = [recvd EXCEPT ![p] = @ \cup M]
  /\ UNCHANGED << correct, faulty, prog, sent >>

\* A process that got the INIT message accepts and ECHOs immediately.
InitAccept(p) ==
  /\ p \in correct
  /\ prog[p] = "idle"
  /\ prog' = [prog EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {<<p, Phi>>}
  /\ recvd' = [recvd EXCEPT ![p] = @ \cup {<<p, Phi>>}]
  /\ UNCHANGED << correct, faulty >>

\* The threshold for sending ECHO but not yet accepting: N-2T.
EchoNoAccept(p) ==
  /\ p \in correct
  /\ prog[p] = "idle"
  /\ Cardinality({m \in recvd[p] : m[2] = Phi}) >= N - 2 * T
  /\ Cardinality({m \in recvd[p] : m[2] = Phi}) < N - T
  /\ prog' = [prog EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, Phi>>}
  /\ recvd' = [recvd EXCEPT ![p] = @ \cup {<<p, Phi>>}]
  /\ UNCHANGED << correct, faulty >>

\* The threshold for sending ECHO and accepting together: N-T.
EchoAndAccept(p) ==
  /\ p \in correct
  /\ prog[p] = "idle"
  /\ Cardinality({m \in recvd[p] : m[2] = Phi}) >= N - T
  /\ prog' = [prog EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {<<p, Phi>>}
  /\ recvd' = [recvd EXCEPT ![p] = @ \cup {<<p, Phi>>}]
  /\ UNCHANGED << correct, faulty >>

AcceptAfterEcho(p) ==
  /\ p \in correct
  /\ prog[p] \in {"echoed", "idle"}
  /\ Cardinality({m \in recvd[p] : m[2] = Phi}) >= N - T
  /\ prog' = [prog EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, faulty, recvd, sent >>

Next ==
  \/ \E p \in 1..N : ReceiveMsgs(p)
  \/ \E p \in 1..N : InitAccept(p)
  \/ \E p \in 1..N : EchoNoAccept(p)
  \/ \E p \in 1..N : EchoAndAccept(p)
  \/ \E p \in 1..N : AcceptAfterEcho(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : ReceiveMsgs(p))
  /\ WF_vars(\E p \in 1..N : InitAccept(p))

CorrLtl == (\A q \in correct : prog[q] = "idle") ~> (\A q \in correct : prog[q] = "accepted")
RelayLtl == (\E q \in correct : prog[q] = "accepted") ~> (\A q \in correct : prog[q] = "accepted")
UnforgLtl == (\A q \in correct : prog[q] = "noinit") ~> (\A q \in correct : prog[q] = "idle")

====