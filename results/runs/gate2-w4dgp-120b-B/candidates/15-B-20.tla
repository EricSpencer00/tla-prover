---- MODULE bcastByz
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0
Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == {<<p, "ECHO">> : p \in Proc \ {1}} \cup {<<1, "ECHO">>}
vars == <<pc, rcvd, sent, Corr, Faulty>>

TypeInv ==
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]

FCInv ==
  /\ Corr \cup Faulty = Proc
  /\ Corr \cap Faulty = {}
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T

InitV0 == [pc EXCEPT ![1] = "V1"]
Init ==
  /\ sent = {}
  /\ pc = [i \in Proc |-> "V0"]
  /\ rcvd = [i \in Proc |-> {}]
  /\ Corr = {1, 2, 3}
  /\ Faulty = {4}

\* Any process can receive any subset of messages that have been sent, plus
\* the byzantine messages it has not seen yet.
Receive(i) ==
  \E msgset \in SUBSET (sent \cup ByzMsgs):
     rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup msgset]

LazyV1(i) == /\ pc[i] = "V0" /\ pc' = [pc EXCEPT ![i] = "V1"] /\ UNCHANGED <<rcvd, sent>> /\ UNCHANGED <<Corr, Faulty>>
Echo(i) ==
  /\ pc[i] = "V1"
  /\ rcvd[i] = {}
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ pc' = [pc EXCEPT ![i] = "SE"]
  /\ UNCHANGED <<rcvd>> /\ UNCHANGED <<Corr, Faulty>>

Step ==
  \/ \E i \in Proc: LazyV1(i) \/ Echo(i) \/ Receive(i)
  \/ UNCHANGED vars

Spec == Init /\ [][Step]_vars

Unforgeable == (pc[1] = "V0") ~> (pc[1] # "V0")
====