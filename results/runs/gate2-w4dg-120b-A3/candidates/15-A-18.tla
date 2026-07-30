---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

AssumeNBound == N <= 10 /\ N >= 4
AssumeTBound == T <= 3 /\ T >= 1
AssumeFBound == F <= 3 /\ F >= 0
AssumeNSysBound == N > 3 * T
AssumeFaultBound == T >= F

VARIABLES correct, faulty, loc, inbox, sent
vars == << correct, faulty, loc, inbox, sent >>

InitLocs == {"initRecv", "noInit", "sawEcho", "echoed", "accepted"}

MsgTypes == {"ECHO"}
Msgs == [snd : 1..N, typ : MsgTypes]

Initialization(k) == IF k <= N - F THEN "initRecv" ELSE "noInit"

TypeOK ==
  /\ correct \subseteq 1..N
  /\ correct # {}
  /\ faulty \subseteq 1..N
  /\ correct \cup faulty = 1..N
  /\ correct \cap faulty = {}
  /\ loc \in [1..N -> InitLocs]
  /\ inbox \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F

Init ==
  /\ correct = { k \in 1..N : k <= N - F }
  /\ faulty = 1..N \ correct
  /\ loc = [k \in 1..N |-> Initialization(k)]
  /\ inbox = [k \in 1..N |-> {}]
  /\ sent = {}

\* correct process k receives a set of fresh messages from any sender
Recv(k) ==
  /\ k \in correct
  /\ loc[k] \notin {"accepted"}
  /\ \E newMsgs \in SUBSET (sent \cup Msgs) :
       inbox' = [inbox EXCEPT ![k] = inbox[k] \cup newMsgs]
  /\ UNCHANGED << correct, faulty, loc, sent >>

\* a process that got the INIT broadcast accepts immediately and ECHOs
EchoInit(k) ==
  /\ k \in correct
  /\ loc[k] = "initRecv"
  /\ loc' = [loc EXCEPT ![k] = "accepted"]
  /\ sent' = sent \cup {[snd |-> k, typ |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, inbox >>

\* a process that did NOT get the broadcast yet may ECHO, but not accept,
\* once it has collected at least N-2T distinct ECHOs but fewer than N-T.
EchoMid(k) ==
  /\ k \in correct
  /\ loc[k] = "noInit"
  /\ Cardinality({ m \in inbox[k] : m.typ = "ECHO" }) >= N - 2 * T
  /\ Cardinality({ m \in inbox[k] : m.typ = "ECHO" }) < N - T
  /\ loc' = [loc EXCEPT ![k] = "echoed"]
  /\ sent' = sent \cup {[snd |-> k, typ |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, inbox >>

\* a process that never got the broadcast may ECHO and accept
\* once it has collected the full quorum of N-T distinct ECHOs.
EchoFull(k) ==
  /\ k \in correct
  /\ loc[k] = "noInit"
  /\ Cardinality({ m \in inbox[k] : m.typ = "ECHO" }) >= N - T
  /\ loc' = [loc EXCEPT ![k] = "accepted"]
  /\ sent' = sent \cup {[snd |-> k, typ |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, inbox >>

AcceptEcho(k) ==
  /\ k \in correct
  /\ loc[k] = "echoed"
  /\ Cardinality({ m \in inbox[k] : m.typ = "ECHO" }) >= N - T
  /\ loc' = [loc EXCEPT ![k] = "accepted"]
  /\ UNCHANGED << correct, faulty, inbox, sent >>

Next ==
  \/ \E k \in 1..N : Recv(k) \/ EchoInit(k) \/ EchoMid(k) \/ EchoFull(k) \/ AcceptEcho(k)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E k \in 1..N : Recv(k))
  /\ WF_vars(\E k \in 1..N : EchoInit(k) \/ EchoMid(k) \/ EchoFull(k) \/ AcceptEcho(k))

CorrLtl == \A k \in correct : (loc[k] = "initRecv") ~> (loc[k] = "accepted")
RelayLtl == (\E k \in correct : loc[k] = "accepted") ~> (\A k \in correct : loc[k] = "accepted")
UnforgLtl == (\A k \in correct : loc[k] = "noInit") ~> (\A k \in correct : loc[k] # "accepted")

====