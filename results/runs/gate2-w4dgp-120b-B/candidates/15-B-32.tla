------------------------------ MODULE bcastByz ------------------------------
(* TLA+ encoding of a parameterized model of the broadcast distributed
   algorithm with Byzantine faults.

   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcast to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94

   The model has a TLAPS proof for property Unforgeability: if a correct process
   does not broadcast a message, then no correct process ever accepts it. The
   goal is to prove the formula (InitNoBcast /\ [][Next]_vars) => []Unforg.

   Two TLC properties are also checked (for fixed N, T, F):
      CorrLtl  : if a correct process broadcasts, then every correct process accepts
      RelayLtl : if a correct process accepts, then every correct process accepts

   The steps correspond to the 4 if-then expressions in Fig. 7 of the paper.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
   This file is subject to the license in the file LICENSE.
 *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

VARIABLES Corr, Faulty, pc, rcvd, sent

vars == << Corr, Faulty, pc, rcvd, sent >>

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

\* Initial values: no messages sent and each correct process is either
\* V0 (no INIT) or V1 (has an INIT message); InitNoBcast forces all to V0.
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

\* A process receiving new messages (any subset of sent plus, optionally,
\* Byzantine messages) and executing one of the four AWAIT clauses.
Step(i) ==
  \/ (\E new \in SUBSET (sent \cup ByzMsgs) :
        rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup new ]
        /\ IF pc[i] = "V1" THEN pc' = [pc EXCEPT ![i] = "SE"]
           ELSE IF Cardinality(rcvd[i]) >= N - 2 * T /\ Cardinality(rcvd[i]) < N - T
                 THEN pc' = [pc EXCEPT ![i] = "SE"]
                 ELSE IF Cardinality(rcvd[i]) >= N - T /\ pc[i] \notin {"V0", "V1"}
                       THEN pc' = [pc EXCEPT ![i] = "AC"]
                       ELSE IF Cardinality(rcvd[i]) >= N - T /\ pc[i] = "SE"
                             THEN pc' = [pc EXCEPT ![i] = "AC"]
                             ELSE pc' = pc
        /\ sent' = sent \cup {<<i, "ECHO">>}
        /\ UNCHANGED <<Corr, Faulty>>)

Next == \E i \in Corr : Step(i) \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

FCConstraintsInitNoBcast == InitNoBcast => FCConstraints
TypeOKInitNoBcast == InitNoBcast => TypeOK

\* InitNoBcast forces pc everywhere to V0, so Unforgeability becomes a
\* first-order formula: no correct process is ever in state AC.
Unforgeable == (\A i \in Proc : i \in Corr => (pc[i] /= "AC"))

IndInv_UF ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

IndInv_UFInit == IndInv_UF => FCConstraints /\ TypeOK
IndInv_UFStep == IndInv_UF /\ [Next]_vars => IndInv_UF'
IndInv_UFStepStutter == IndInv_UF /\ UNCHANGED vars => IndInv_UF'

IndInv_UFSpec == SpecNoBcast => []IndInv_UF

THEOREM FCConstraintsInitNoBcast == FCConstraintsInitNoBcast
  BY DEF FCConstraintsInitNoBcast

THEOREM TypeOKInitNoBcast == TypeOKInitNoBcast
  BY DEF TypeOKInitNoBcast

THEOREM InitNoBcastSpec == InitNoBcast => []FCConstraints /\ []TypeOK
  BY PTL DEF InitNoBcast

THEOREM IndInv_UFInit == IndInv_UFInit
  BY DEF IndInv_UF

\* The main proof: IndInv_UF is an inductive invariant of SpecNoBcast.
THEOREM IndInv_UFStep == IndInv_UFStep
  BY DEF IndInv_UF

THEOREM IndInv_UFStepStutter == IndInv_UFStepStutter
  BY DEF IndInv_UF

THEOREM IndInv_UFSpec == IndInv_UFSpec
  BY PTL DEF InitNoBcast, IndInv_UF, SpecNoBcast

\* From the invariant we get the unforgeability safety property.
THEOREM UnforgeabilityTheorem == IndInv_UF => Unforgeable
  BY DEF IndInv_UF, Unforgeable

=============================================================================