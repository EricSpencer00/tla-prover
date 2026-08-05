------------------------------ MODULE bcastByz ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast distributed 
   algorithm with Byzantine faults.
   This is a one-round version of asynchronous reliable broadcast from:
   T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987.
   See the accompanying proof for property Unforgeability: if a correct
   process does not broadcast a message, no correct process accepts it.
   The goal is to prove (InitNoBcast /\ [][Next]_vars) => []Unforg.
   Two properties are checked by TLC: CorrLtl (correct broadcast reaches
   all correct processes) and ReplayLtl (acceptance is contagious).
*)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
          FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F)

Proc == 1..N
M == { "ECHO" }
ByzMsgs == (1..F) \X M
vars == <<pc, rcvd, sent, Corr, Faulty>>

\* Sent is witnessed only at correct processes; pc models whether a process
\* has received an INIT message from a broadcaster (V1) or not (V0).
TypeOK ==
  /\ pc \in [Proc -> {"V0","V1","SE","AC"}]
  /\ sent \subseteq Proc \X M
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]

FCConstraints ==
  /\ Corr \cup Faulty = Proc /\ Cardinality(Corr) >= N - T /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M

\* Sender i receives all messages sent by correct processes and optionally all
\* byzantine ones; includeByz chooses whether to include the latter.
Receive(i, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [j \in Proc |-> IF j = i THEN rcvd[i] \cup new ELSE rcvd[j]]

\* Once correct p has received an INIT, it sends ECHO to all; these are the
\* first-step actions of the one-round broadcast.
UponV1(p) ==
  /\ pc[p] = "V1"
  /\ pc' = [pc EXCEPT ![p] = "SE"]
  /\ sent' = sent \cup {<<p,"ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

\* A correct process that has not yet accepted, with sufficient messages
\* from others, accepts and relays its own ECHO.
UponAccept(p) ==
  /\ Cardinality(rcvd'[p]) >= N - T /\ pc[p] \in {"SE","V0","V1"}
  /\ pc' = [pc EXCEPT ![p] = "AC"]
  /\ sent' = sent \cup {<<p,"ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

\* A correct process that has not yet accepted, with fewer messages, relays.
UponNonFaulty(p) ==
  /\ Cardinality(rcvd'[p]) >= N - 2 * T
  /\ pc' = [pc EXCEPT ![p] = "SE"]
  /\ sent' = sent \cup {<<p,"ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

Step(p) ==
  \/ Receive(p, TRUE) /\ (UponV1(p) \/ UponNonFaulty(p) \/ UponAccept(p))
  \/ UNCHANGED <<pc, sent, Corr, Faulty>>

Next == \E p \in Corr : Step(p) \/ UNCHANGED vars

SpecNoBcast == Init /\ [][Next]_vars
Init == /\ Corr \subseteq Proc /\ Faulty = Proc \ Corr
         /\ pc \in [Proc -> {"V0","V1"}] /\ sent = {} /\ rcvd = [p \in Proc |-> {}]

\* InitNoBcast models the case where the transmitter never broadcasts: no
\* correct process receives an INIT message.
InitNoBcast == Init /\ pc = [p \in Proc |-> "V0"]
Unforgeable == (\A p \in Corr : pc[p] # "AC")

\* An inductive invariant that captures InitNoBcast in a strength suitable
\* for checking with TLC: the state is all V0's with nothing sent.
IndInv ==
  /\ TypeOK /\ FCConstraints /\ sent = {} /\ pc = [p \in Proc |-> "V0"]

SpecNoBcastInit == InitNoBcast /\ [][Next]_vars

=============================================================================