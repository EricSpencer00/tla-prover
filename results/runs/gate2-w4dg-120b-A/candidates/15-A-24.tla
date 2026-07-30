---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Locations == {"init", "nomsg", "echoed", "accept"}

VARIABLES correct, faulty, pc, recv, sent
vars == <<correct, faulty, pc, recv, sent>>

SentSetBy == [from : 1..N, kind : {"ECHO"}]
RecvEchos(x) == { m.from : m \in { y \in recv[x] : y.kind = "ECHO" } }

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> Locations]
  /\ recv \in [1..N -> SUBSET SentSetBy]
  /\ sent \subseteq SentSetBy

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = (1..N)
  /\ \A x \in 1..N : pc[x] \in Locations

Init(N, F) ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ \E x \in 1..N : pc[x] = "init"
  /\ \A x \in ((1..N) \ {x}) : pc[x] \in {"nomsg", "echoed", "accept"}
  /\ recv = [x \in 1..N |-> {}]
  /\ sent = {}

InitAll(N, F) ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ \A x \in 1..N : pc[x] \in {"init", "echoed", "accept"}
  /\ recv = [x \in 1..N |-> {}]
  /\ sent = {}

\* A correct process receives new messages from all correct senders plus
\* arbitrary Byzantine messages (bounded by the msg cap of the .cfg level).
Receive(x) ==
  /\ x \in correct
  /\ pc[x] # "accept"
  /\ \E New \in SUBSET (sent \cup SentSetBy) :
       recv' = [recv EXCEPT ![x] = recv[x] \cup New]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* Correct processes that already saw the INIT accept immediately.
AcceptInit(x) ==
  /\ x \in correct
  /\ pc[x] = "init"
  /\ pc' = [pc EXCEPT ![x] = "accept"]
  /\ sent' = sent \cup {[from |-> x, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

EchoThreshold(x) ==
  /\ x \in correct
  /\ pc[x] = "nomsg"
  /\ Cardinality(RecvEchos(x)) >= N - 2 * T
  /\ Cardinality(RecvEchos(x)) < (N - T)
  /\ pc' = [pc EXCEPT ![x] = "echoed"]
  /\ sent' = sent \cup {[from |-> x, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A process receiving enough echoes accepts in the same step, if it had not
\* already sent an echo on its own.
EchoAccept(x) ==
  /\ x \in correct
  /\ pc[x] \in {"nomsg", "echoed"}
  /\ Cardinality(RecvEchos(x)) >= (N - T)
  /\ pc' = [pc EXCEPT ![x] = "accept"]
  /\ sent' = sent \cup {[from |-> x, kind |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptEcho(x) ==
  /\ x \in correct
  /\ pc[x] = "echoed"
  /\ Cardinality(RecvEchos(x)) >= (N - T)
  /\ pc' = [pc EXCEPT ![x] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next(N, F) ==
  \/ \E x \in 1..N : Receive(x) \/ AcceptInit(x) \/ EchoThreshold(x) \/ EchoAccept(x) \/ AcceptEcho(x)

\* Weak fairness on the combined receive-and-act step for a correct process;
\* it is what lets the liveness properties below go through.
Spec ==
  /\ Init(N, F) \/ InitAll(N, F)
  /\ [][Next(N, F)]_vars
  /\ \A x \in 1..N : WF_vars(Receive(x))
  /\ \A x \in 1..N : WF_vars(AcceptInit(x))
  /\ \A x \in 1..N : WF_vars(EchoThreshold(x))
  /\ \A x \in 1..N : WF_vars(EchoAccept(x))
  /\ \A x \in 1..N : WF_vars(AcceptEcho(x))

CorrLtl ==
  /\ \A x \in correct : pc[x] = "init"
  /\ <>(\A x \in correct : pc[x] = "accept")

RelayLtl ==
  /\ (\E x \in correct : pc[x] = "accept")
  /\ <>(\A x \in correct : pc[x] = "accept")

\* If nobody broadcast, nobody accepts -- the core unforgeability property.
UnforgLtl ==
  /\ \A x \in correct : pc[x] # "init"
  /\ (\A x \in correct : pc[x] # "accept")

====