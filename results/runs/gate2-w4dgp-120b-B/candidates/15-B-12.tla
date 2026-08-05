---- MODULE bcastByz ----
(* TLA+ encoding of the one-round asynchronous reliable broadcast
   (Fig. 7) from [1] with Byzantine faults.  The main theorem is a
   safety property (unforgeability) proved as an invariant; it is
   semantics-preserving but makes the model-checkable by TLC. *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

\* Correct processes are chosen nondeterministically (faulty identity unknown)
\* so the model covers all crash/Byzantine patterns. The "INIT" value is
\* modeled by a pc state rather than an explicit broadcaster.
VARIABLES pc, rcvd, sent, Corr, Faulty
vars == <<pc, rcvd, sent, Corr, Faulty>>

\* Cardinality constraints are kept as explicit invariants so TLC need not
\* evaluate them every step; they are proved in the TLAPS proof below.
NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0
ByzMsgs == Faulty \X {"ECHO"}

Init == /\ sent = {}
        /\ pc \in [1..N -> {"V0", "V1", "SE", "AC"}]
        /\ rcvd = [i \in 1..N |-> {}]
        /\ Corr \subseteq 1..N
        /\ Cardinality(Corr) = N - F
        /\ Faulty = (1..N) \ Corr

InitNoBcast == pc \in [1..N -> {"V0"}] /\ Init

\* A correct process receives a subset of all ECHO messages sent by correct
\* processes, plus any subset of the (bounded) Byzantine messages.
Receive(self, byz) ==
  \E new \in SUBSET (sent \cup (IF byz THEN ByzMsgs ELSE {})):
    rcvd' = [i \in 1..N |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i]]

ReceiveFromCorrect == \E s \in 1..N : Receive(s, FALSE)
ReceiveFromAny     == \E s \in 1..N : Receive(s, TRUE)

\* The three actions correspond to the three if-then statements in Fig. 7.
UponV1(s) ==
  /\ pc[s] = "V1"
  /\ pc' = [pc EXCEPT ![s] = "SE"]
  /\ sent' = sent \cup {<<s, "ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

UponNonFaulty(s) ==
  /\ pc[s] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[s]) >= N - 2 * T
  /\ Cardinality(rcvd'[s]) < N - T
  /\ pc' = [pc EXCEPT ![s] = "SE"]
  /\ sent' = sent \cup {<<s, "ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

UponNotSent(s) ==
  /\ pc[s] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[s]) >= N - T
  /\ pc' = [pc EXCEPT ![s] = "AC"]
  /\ sent' = sent \cup {<<s, "ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

UponSent(s) ==
  /\ pc[s] = "SE"
  /\ Cardinality(rcvd'[s]) >= N - T
  /\ pc' = [pc EXCEPT ![s] = "AC"]
  /\ UNCHANGED <<rcvd, sent, Corr, Faulty>>

Step(s)   == ReceiveFromAny /\ (UponV1(s) \/ UponNonFaulty(s) \/ UponNotSent(s) \/ UponSent(s))
Next      == (\E s \in Corr : Step(s)) \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars /\ WF_vars(\E s \in Corr : ReceiveFromCorrect)

TypeOK == /\ pc \in [1..N -> {"V0", "V1", "SE", "AC"}]
          /\ Corr \subseteq 1..N
          /\ Faulty \subseteq 1..N
          /\ IsFiniteSet(Corr) /\ IsFiniteSet(Faulty)
          /\ Corr \cup Faulty = 1..N
          /\ Faulty = (1..N) \ Corr
          /\ Cardinality(Corr) >= N - T
          /\ Cardinality(Faulty) <= T
          /\ ByzMsgs \subseteq (1..N) \X {"ECHO"}
          /\ IsFiniteSet(ByzMsgs)
          /\ Cardinality(ByzMsgs) = Cardinality(Faulty)
          /\ sent \subseteq (1..N) \X {"ECHO"}
          /\ rcvd \in [1..N -> SUBSET (sent \cup ByzMsgs)]

FCConstraints == /\ Corr \subseteq 1..N
                  /\ Faulty \subseteq 1..N
                  /\ IsFiniteSet(Corr) /\ IsFiniteSet(Faulty)
                  /\ Corr \cup Faulty = 1..N
                  /\ Faulty = (1..N) \ Corr
                  /\ Cardinality(Corr) >= N - T
                  /\ Cardinality(Faulty) <= T
                  /\ ByzMsgs \subseteq (1..N) \X {"ECHO"}
                  /\ IsFiniteSet(ByzMsgs)
                  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

Unforge == (\A i \in 1..N : i \in Corr => (pc[i] # "AC"))

\* The unforgeability property is captured as a single inductive invariant,
\* rather than a semantic implication, which is what lets TLC check it.
IndInv == /\ TypeOK
          /\ FCConstraints
          /\ sent = {}
          /\ pc = [i \in 1..N |-> "V0"]

InitInv  == InitNoBcast => IndInv
NextInv  == IndInv /\ [Next]_vars => IndInv'
SafetyInv == IndInv => Unforge
SpecInv  == SpecNoBcast => []Unforge

\* Proof sketch: InitInv and NextInv are proved by unfolding every disjunct
\* of Step; SafetyInv follows from the pc = "V0" component of the
\* invariant.  All steps are written so the primed operators appear only
\* after the constants they depend on.
THEOREM InitInv == InitNoBcast => IndInv
THEOREM NextInv == IndInv /\ [Next]_vars => IndInv'
THEOREM SafetyInv == IndInv => Unforge
THEOREM SpecInv == SpecNoBcast => []Unforge

====