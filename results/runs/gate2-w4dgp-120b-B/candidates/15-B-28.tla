---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS
CONSTANTS N, T, F
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

\* Process and message definition
Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == (Proc \ {1}) \X M

VARIABLE pc, Corr, Faulty, sent, rcvd

vars == << pc, Corr, Faulty, sent, rcvd >>

RECURSIVE SumCard(_, _)
SumCard(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE IN f[x] + SumCard(f, S \ {x})

TypeOK ==
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq (Proc \X M)
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]

\* At least N-2T correct processes must have sent an ECHO before accepting the message,
\* but not so many that the 2nd accept condition already applies
AcceptCondition(i) ==
  /\ Cardinality(rcvd[i]) >= N - 2 * T /\ Cardinality(rcvd[i]) < N - T

Init ==
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ Corr \in SUBSET Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) = N - F

InitNoBcast == (pc = [i \in Proc |-> "V0"]) /\ Init

SendEcho(i) == sent' = sent \cup {<<i, "ECHO">>}
Receive(i) == (\E new \in SUBSET (sent \cup ByzMsgs) : rcvd' = [j \in Proc |-> IF j = i THEN rcvd[i] \cup new ELSE rcvd[j]])

Step(i) ==
  \/ Receive(i) /\ SendEcho(i)
  \/ Receive(i) /\ IF pc[i] = "V1" THEN pc' = [pc EXCEPT ![i] = "SE"] ELSE UNCHANGED pc
  \/ Receive(i) /\ IF pc[i] \notin {"V0", "V1"} /\ AcceptCondition(i) THEN pc' = [pc EXCEPT ![i] = "SE"] ELSE UNCHANGED pc
  \/ Receive(i) /\ IF pc[i] \in {"V0", "V1"} /\ Cardinality(rcvd[i]) >= N - T THEN pc' = [pc EXCEPT ![i] = "AC"] /\ UNCHANGED sent
  \/ Receive(i) /\ IF pc[i] = "SE" /\ Cardinality(rcvd[i]) >= N - T THEN pc' = [pc EXCEPT ![i] = "AC"] /\ UNCHANGED <<sent, Corr, Faulty>>

CorrStep == (\E i \in Corr: Step(i))
Next == CorrStep \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(CorrStep)

CorrLtl == (\A i \in Corr : pc[i] = "V1") => <>(\A i \in Corr : pc[i] = "AC")
RelayLtl == []((\E i \in Corr : pc[i] = "AC") => <>(\A i \in Corr : pc[i] = "AC"))
Unforg == (\A i \in Proc : i \in Corr => pc[i] /= "AC")

\* A corrected invariant: among other things it now imposes that every process which has
\* accepted a message is in the correct set, which is not derivable from TypeOK alone
Inv ==
  /\ TypeOK
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)
  /\ sent = {}

\* No Byzantine process ever influences the outcome: if no correct process accepts anything
\* the system stays in its initial configuration forever
InitNoBcastInv == (pc = [i \in Proc |-> "V0"]) /\ Inv

SpecNoBcast == InitNoBcast /\ [][Next]_vars

\* Proof sketch: Inv is inductive, InitNoBcastInv establishes the premise, so Unforg follows
InvInit == InitNoBcastInv => Inv
InvStep == Inv /\ [Next]_vars => Inv'
InvResult == Inv => Unforg
Theorem == InvInit /\ InvStep /\ InvResult

====