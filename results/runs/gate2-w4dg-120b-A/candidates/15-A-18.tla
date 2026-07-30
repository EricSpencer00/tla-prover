---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* Broadcast with Byzantine faults, based on Srikanth & Toueg 1987 (Fig 7).
\* Init state is parameterized: either some correct process starts with the
\* broadcaster's INIT message or none do, covering both the normal and the
\* "no correct broadcast" safety case.
\* Each correct process sends at most one ECHO message, tracking who has sent.

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent
vars == << correct, faulty, pc, recv, sent >>

TX == { "ECHO" }

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ correct # {}
  /\ Cardinality(correct) = (N - F)
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> { "idle", "hasInit", "sent", "accepted" }]
  /\ recv \in [1..N -> SUBSET ((1..N) \X TX)]
  /\ sent \in SUBSET ((1..N) \X TX)

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

Init ==
  /\ correct = (CHOOSE c \subseteq (1..N) : Cardinality(c) = (N - F))
  /\ faulty = (1..N) \ correct
  /\ pc = [p \in (1..N) |-> IF p \in correct THEN "idle" ELSE "idle"]
  /\ recv = [p \in (1..N) |-> {}]
  /\ sent = {}

\* No-correct-broadcast configuration: all correct processes start idle.
InitNoBroadcast ==
  /\ Init
  /\ pc' = [p \in (1..N) |-> IF p \in correct THEN "idle" ELSE "idle"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

\* A correct process receives a (possibly empty) set of fresh messages, drawn
\* from everything sent by correct processes plus anything from Byzantine.
Receive(p, m) ==
  /\ p \in correct
  /\ pc[p] \in { "idle", "hasInit" }
  /\ m \subseteq ((sent \cap (correct \X TX)) \cup (faulty \X TX))
  /\ m # {}
  /\ recv' = [recv EXCEPT ![p] = @ \cup m]
  /\ UNCHANGED << correct, faulty, pc, sent >>

Sends(p) == { p } \X TX

\* A correct process with the INIT message accepts immediately and echoes.
AcceptsBroadcast(p) ==
  /\ p \in correct
  /\ pc[p] = "hasInit"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup Sends(p)
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent an ECHO, with enough ECHOs seen,
\* sends its ECHO but keeps accepting pending.
Echoes(p) ==
  /\ p \in correct
  /\ pc[p] = "idle"
  /\ Cardinality(recv[p] \cap (correct \X TX)) >= (N - 2 * T)
  /\ Cardinality(recv[p] \cap (correct \X TX)) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup Sends(p)
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent an ECHO, with the final quorum
\* of ECHOs seen, sends its ECHO and accepts.
EchoesAndAccepts(p) ==
  /\ p \in correct
  /\ pc[p] = "idle"
  /\ Cardinality(recv[p] \cap (correct \X TX)) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup Sends(p)
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has already sent an ECHO accepts once the final
\* quorum of ECHOs is seen.
Accepts(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality(recv[p] \cap (correct \X TX)) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

ReceiveAny(p) == \E m \in (SUBSET ((1..N) \X TX)) : Receive(p, m)

Next ==
  \/ \E p \in (1..N) : ReceiveAny(p)
  \/ \E p \in (1..N) : AcceptsBroadcast(p)
  \/ \E p \in (1..N) : Echoes(p)
  \/ \E p \in (1..N) : EchoesAndAccepts(p)
  \/ \E p \in (1..N) : Accepts(p)

InitAllBroadcast ==
  /\ Init
  /\ pc' = [p \in (1..N) |-> IF p \in correct THEN "hasInit" ELSE "idle"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

Spec ==
  /\ InitAllBroadcast
  /\ [][Next]_vars
  /\ WF_vars(\E p \in (1..N) : ReceiveAny(p))
  /\ WF_vars(\E p \in (1..N) : AcceptsBroadcast(p))
  /\ WF_vars(\E p \in (1..N) : Echoes(p))
  /\ WF_vars(\E p \in (1..N) : EchoesAndAccepts(p))
  /\ WF_vars(\E p \in (1..N) : Accepts(p))

\* No correct process accepts unless some correct process broadcasted.
UnforgLtl == (\A p \in correct : pc[p] # "hasInit") ~> (\A p \in correct : pc[p] # "accepted")

CorrLtl == (\A p \in correct : pc[p] = "hasInit") ~> (\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")

====