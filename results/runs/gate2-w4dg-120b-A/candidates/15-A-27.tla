---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Process i starts with or without the broadcaster's INIT message, which is
\* represented by its control location.  Correct processes obey the protocol;
\* Byzantine processes may send arbitrary messages.
VARIABLES correct, faulty, pc, rcv, sent

Bump(x) == IF x < 2 THEN x + 1 ELSE 2
Range(S) == { S[i] : i \in DOMAIN S }
Obtain(f, S) == UNION { f[x] : x \in S }

\* Distinct senders of message m that any correct process has heard about.
DistinctBy(m) ==
  { y \in correct : \E z \in rcv[y] : z[1] = y /\ z[2] = m }

InitState(N, F) == CHOOSE R \in SUBSET (1..N) : Cardinality(R) = N - F

Msg(m) == [o \in 1..N |-> [m |-> m, o |-> o]]
Msgs == { Msg(m)[o] : m \in {"init", "echo"} : o \in 1..N }

Init ==
  /\ correct = InitState(N, F)
  /\ faulty = (1..N) \ correct
  /\ pc = [i \in 1..N |-> IF i \in correct THEN 0 ELSE 2]
  /\ rcv = [i \in 1..N |-> {}]
  /\ sent = {}

RestrictedInit ==
  /\ Init
  /\ \A i \in correct : pc[i] = 0

\* ANY receives messages from correct and from Byzantine processes together.
Receive ==
  /\ \E M \in SUBSET (sent \cup Msgs) :
       \E i \in correct :
         /\ pc[i] < 2
         /\ rcv' = [rcv EXCEPT ![i] = @ \cup M]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(i) ==
  /\ sent' = sent \cup { Msg("echo")[i] }
  /\ pc' = [pc EXCEPT ![i] = Bump(@)]

\* A correct process that received the broadcaster's INIT message accepts and
\* informs everyone.
ActBroadcast(i) ==
  /\ pc[i] = 0
  /\ SendEcho(i)
  /\ pc' = [pc EXCEPT ![i] = 2]

ActRelay(i) ==
  /\ pc[i] = 0
  /\ Cardinality(DistinctBy("echo")) >= N - 2 * T
  /\ Cardinality(DistinctBy("echo")) < N - T
  /\ SendEcho(i)

ActAccept(i) ==
  /\ pc[i] = 0
  /\ Cardinality(DistinctBy("echo")) >= N - T
  /\ SendEcho(i)
  /\ pc' = [pc EXCEPT ![i] = 2]

ActLate(i) ==
  /\ pc[i] = 1
  /\ Cardinality(DistinctBy("echo")) >= N - T
  /\ pc' = [pc EXCEPT ![i] = 2]

Next ==
  \/ Receive
  \/ \E i \in 1..N :
       \/ ActBroadcast(i) \/ ActRelay(i) \/ ActAccept(i) \/ ActLate(i)
  \/ UNCHANGED <<correct, faulty, pc, rcv, sent>>

Spec ==
  /\ Init
  /\ [][Next]_<<correct, faulty, pc, rcv, sent>>
  /\ WF_<<correct, faulty, pc, rcv, sent>>(Receive)

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ correct \cap faulty = {}
  /\ pc \in [1..N -> 0..2]
  /\ rcv \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs

FCConstraints == Cardinality(correct) = N - F

CorrLtl == (\A i \in correct : pc[i] = 0) ~> (\A i \in correct : pc[i] = 2)
RelayLtl == (\E i \in correct : pc[i] = 2) ~> (\A i \in correct : pc[i] = 2)
UnforgLtl == RestrictedInit ~> (\A i \in correct : pc[i] = 0)

====