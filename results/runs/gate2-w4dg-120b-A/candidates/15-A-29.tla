---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES phase, inbox, sent, correct, faulty
vars == <<phase, inbox, sent, correct, faulty>>

Echomsgs == {1 .. N}
States == {"notrcvd", "rcvd", "echoed", "acc"}

TypeOK ==
  /\ phase \in [1 .. N -> States]
  /\ inbox \in [1 .. N -> SUBSET Echomsgs]
  /\ sent \subseteq Echomsgs
  /\ correct \subseteq 1 .. N
  /\ faulty \subseteq 1 .. N

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = 1 .. N
  /\ phase \in [1 .. N -> States]

InitState ==
  /\ phase = [p \in 1 .. N |-> IF p <= N - F THEN "rcvd" ELSE "notrcvd"]
  /\ inbox = [p \in 1 .. N |-> {}]
  /\ sent = {}
  /\ correct = {p \in 1 .. N : p <= N - F}
  /\ faulty = {p \in 1 .. N : p > N - F}

InitStateEmpty ==
  /\ phase = [p \in 1 .. N |-> "notrcvd"]
  /\ inbox = [p \in 1 .. N |-> {}]
  /\ sent = {}
  /\ correct = {p \in 1 .. N : p <= N - F}
  /\ faulty = {p \in 1 .. N : p > N - F}

\* Messages from correct processes are exactly the ECHO messages they sent;
\* faulty processes may add any message not already sent.
Delivered(p) ==
  inbox[p] \cup
    \E S \in [1 .. N -> SUBSET Echomsgs] :
      /\ \A q \in correct : S[q] \subseteq sent
      /\ \A q \in faulty : S[q] = {}
      /\ inbox[p] \cup S[p]

Receive(p) ==
  /\ \E m \in Delivered(p) : inbox' = [inbox EXCEPT ![p] = m]
  /\ UNCHANGED <<phase, sent, correct, faulty>>

\* A correct process that got the broadcast implicitly accepts and sends an ECHO.
BroadcastAccept(p) ==
  /\ phase[p] \in {"rcvd", "notrcvd"}
  /\ phase' = [phase EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {p}
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {p}]
  /\ UNCHANGED <<correct, faulty>>

\* The two ECHO thresholds from Srikanth and Toueg's algorithm.
Relay(p) ==
  /\ phase[p] = "notrcvd"
  /\ Cardinality(inbox[p]) >= N - 2 * T
  /\ Cardinality(inbox[p]) < N - T
  /\ phase' = [phase EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {p}
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {p}]
  /\ UNCHANGED <<correct, faulty>>

AcceptRelay(p) ==
  /\ phase[p] = "notrcvd"
  /\ Cardinality(inbox[p]) >= N - T
  /\ phase' = [phase EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {p}
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {p}]
  /\ UNCHANGED <<correct, faulty>>

AcceptEcho(p) ==
  /\ phase[p] = "echoed"
  /\ Cardinality(inbox[p]) >= N - T
  /\ phase' = [phase EXCEPT ![p] = "acc"]
  /\ UNCHANGED <<sent, inbox, correct, faulty>>

Serv(p) ==
  \/ Receive(p) \/ BroadcastAccept(p) \/ Relay(p) \/ AcceptRelay(p) \/ AcceptEcho(p)

Next ==
  \E p \in 1 .. N : Serv(p)

Spec ==
  /\ (InitState \/ InitStateEmpty)
  /\ [][Next]_vars
  /\ WF_vars(Serv(N))

UnforgLtl ==
  (InitStateEmpty => (\A p \in correct : phase[p] = "acc"))

CorrLtl ==
  (InitState => (\A p \in correct : phase[p] = "acc"))

RelayLtl ==
  (InitState /\ \E p \in correct : phase[p] = "acc") ~> (\A p \in correct : phase[p] = "acc")
====