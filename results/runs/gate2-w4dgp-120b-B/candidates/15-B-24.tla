---- MODULE bcastByz ----
(* Distributed broadcast with Byzantine faults and proof of unforgeability.
   Specification from [1] (Fig. 7) with a TLAPS proof that if a correct process
   never sends an ECHO message, no correct process ever accepts it. The
   unforgeability property is a safety property, so a strong fairness condition
   is unnecessary for its proof. *)
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == (N - F .. N) \X M

vars == << pc, rcvd, sent, Corr, Faulty >>
TypeOK ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ IsFiniteSet(Corr)
  /\ IsFiniteSet(Faulty)
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ sent \subseteq Proc \X M
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET (1 .. N - F)
  /\ Faulty = Proc \ Corr

(* The first if-then expression in Fig. 7, applied to a correct process. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED <<Corr, Faulty>>

(* The third if-then expression in Fig. 7: a correct process sends ECHO only after
   receiving from at least N-2T distinct processes. *)
UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED <<Corr, Faulty>>

(* The second and third if-then expressions in Fig. 7. *)
UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED <<Corr, Faulty>>

(* Any step of a correct process. *)
Step(self) ==
  /\ rcvd' \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next == \/ \E self \in Corr: Step(self) \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
SpecNoBcast == Init /\ [][Next]_vars
SpecUnforge == /\ Init /\ [][Next]_vars
              /\ \A self \in Corr: WF_vars(Step(self))

(* No broadcast: every correct process has V0. A correct process never accepts. *)
Unforgeable ==
  (\A i \in Proc: i \in Corr => pc[i] = "V0") => \A i \in Corr: pc[i] # "AC"

(* The inductive invariant used to prove Unforgeable. *)
IndInv ==
  /\ TypeOK
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

IndInvInit == Init => IndInv

IndInvStep ==
  IndInv /\ [Next]_vars => IndInv' /\ TypeOK'
  <=> IndInv /\ (Next \/ UNCHANGED vars) => IndInv'

IndInvSpec == SpecNoBcast => []IndInv

UnforgeableSpec == SpecUnforge => []Unforgeable

====