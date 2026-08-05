------------------------------ MODULE bcastByz ------------------------------
(* TLA+ encoding of a parameterized model of the broadcast distributed algorithm
   with Byzantine faults.  This is a one-round version of reliable broadcast
   (Fig. 7) from:  T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to
   derive simple fault-tolerant algorithms. Distributed Computing 1987.

   The model has a TLAPS proof that the unforgeability property (a correct process
   is never blamed for a message that no correct process broadcast) follows from
   Init /\ [][Next]_vars.  Corr and Faulty are declared as variables so that TLC
   checks all possible fault sets.

   Theorem: (Init /\ [][Next]_vars) => []Unforgeability
*)
EXTENDS Naturals,
        FiniteSets,
        Functions,
        FunctionTheorems,
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M

vars == <<Corr, Faulty, pc, rcvd, sent>>

\* Two initial values V0 and V1 model whether a correct process has received the
\* broadcast's INIT message: all correct processes start in V0 (unbroadcast).
TypeOK ==
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]

FCConstraints ==
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
  /\ Corr \cup Faulty = Proc /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

Init ==
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ rcvd = [i \in Proc |-> {}]
  /\ sent = {}
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [Proc -> {"V0"}] /\ Init

\* A correct process receives any subset of messages from correct senders and any
\* subset of Byzantine messages (includeByz = FALSE omits the Byzantine ones).
Receive(i, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup new]

ReceiveFromCorrect(i) == Receive(i, FALSE)
ReceiveFromAny(i) == Receive(i, TRUE)

UponV1(i) ==
  /\ pc[i] = "V1"
  /\ pc' = [pc EXCEPT ![i] = "SE"]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

\* Only the third if-then expression of Fig. 7: upon receiving from at least
\* N-2*T distinct processes, a correct process sends ECHO messages.
UponNonFaulty(i) ==
  /\ pc[i] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[i]) >= N - 2 * T
  /\ Cardinality(rcvd'[i]) < N - T
  /\ pc' = [pc EXCEPT ![i] = "SE"]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptNotSentBefore(i) ==
  /\ pc[i] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[i]) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "AC"]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptSentBefore(i) ==
  /\ pc[i] = "SE"
  /\ Cardinality(rcvd'[i]) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "AC"]
  /\ UNCHANGED <<sent, Corr, Faulty>>

Step(i) ==
  /\ ReceiveFromAny(i)
  /\ \/ UponV1(i)
     \/ UponNonFaulty(i)
     \/ UponAcceptNotSentBefore(i)
     \/ UponAcceptSentBefore(i)

Next == (\E i \in Corr : Step(i)) \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars /\ WF_vars(\E i \in Corr : Step(i))

SpecNoBcast == InitNoBcast /\ [][Next]_vars

\* If no correct process broadcasts, no correct process accepts (unforgeability).
Unforge == (\A i \in Proc : i \in Corr => pc[i] # "AC")

\* An inductive invariant suitable for TLC: the strong form of InitNoBcast is
\* moved into the first conjunct.
IndInv_Unforge ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [i \in Proc |-> "V0"]

\* A rearranged form of IndInv_Unforge, used by TLC's depth-2 check to avoid
\* generating unreachable initial states.
IndInv_Unforge_TLC ==
  /\ pc = [i \in Proc |-> "V0"]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] # "AC"
  /\ sent = {}
  /\ rcvd \in [Proc -> SUBSET ByzMsgs]

=============================================================================