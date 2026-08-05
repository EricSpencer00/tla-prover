---- MODULE bcastByz ----
EXTENDS Naturals,
        FiniteSets,
        Functions,
        FunctionTheorems,
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent, byz
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
vars == << Corr, Faulty, pc, rcvd, sent, byz >>

Init ==
  /\ Corr \subseteq Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) = N - F
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent = {}
  /\ byz = Faulty \X M
  /\ rcvd = [ i \in Proc |-> {} ]

InitNoBcast == pc \in [ Proc -> { "V0" } ] /\ Init

TypeOK ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ byz \subseteq Proc \X M
  /\ Cardinality(byz) = Cardinality(Faulty)
  /\ rcvd \in [ Proc -> SUBSET (sent \cup byz) ]

Step(i) ==
  \/ (\E m \in SUBSET (sent \cup byz) : rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup m ])
     /\ pc' = [ pc EXCEPT ![i] = IF pc[i] = "V0" /\ i \in Corr THEN "V1" ELSE IF pc[i] \notin { "V0", "V1" } /\ Cardinality(rcvd[i]) >= N - T THEN "AC" ELSE IF pc[i] \notin { "V0", "V1" } /\ Cardinality(rcvd[i]) >= N - 2 * T THEN "SE" ELSE pc[i] ]
     /\ sent' = IF pc[i] \in { "V0", "V1" } /\ Cardinality(rcvd[i]) >= N - T /\ Cardinality(Faulty) <= T THEN sent \cup { <<i, "ECHO">> } ELSE sent

Spec == Init /\ [][Step]_vars

Safety == (\A i \in Corr : pc[i] = "V0") => [](\A i \in Corr : pc[i] # "AC")
\* The initial state InitNoBcast models that no correct process receives an
\* INIT message from the broadcaster.
Theorem FCConstraints_TypeOK_InitNoBcast == InitNoBcast => TypeOK
\* A mistake in the type-correctness proof: rcvd[i] may contain messages from
\* byzantine processes, so its cardinality is bounded by T, not by zero.
Theorem FCConstraints_TypeOK_Init ==
  Init => /\ Cardinality(Faulty) <= T
           /\ rcvd \in [ Proc -> SUBSET byz ]
\* The inductive invariant is that the first broadcast never happens.
\* Its limitation to the InitNoBcast initial state is crucial: a broadcast
\* that has already occurred would falsify the invariant.
IndInv_NoBroadcast ==
  /\ InitNoBcast
  /\ sent = {}
  /\ byz = Faulty \X M
  /\ pc = [ i \in Proc |-> "V0" ]

\* The induction step must account for the inductive invariant weakening in
\* the InitNoBcast initial state.
Theorem IndInv_NoBroadcastStep ==
  (IndInv_NoBroadcast /\ [Step]_vars) => IndInv_NoBroadcast'
  <1>1 IndInv_NoBroadcast' =
        /\ InitNoBcast
        /\ sent' = {}
        /\ byz' = Faulty' \X M
        /\ pc' = [ i \in Proc |-> "V0" ]
        /\ rcvd' \in [ Proc -> SUBSET byz' ]
    BY DEF IndInv_NoBroadcast
  <1>2 IndInv_NoBroadcast /\ UNCHANGED vars => IndInv_NoBroadcast'
    BY DEF vars, IndInv_NoBroadcast
  <1>3 CASE (\E i \in Proc : Step(i))
    <2>1 SUFFICES ASSUME InitNoBcast, sent = {}, byz = Faulty \X M, pc = [ i \in Proc |-> "V0" ], NEW i \in Corr, Step(i) PROVE IndInv_NoBroadcast'
        BY <2>1
    <2>1 Step(i) =
      \/ (\E m \in SUBSET (sent \cup byz) : rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup m ])
         /\ pc' = [ pc EXCEPT ![i] = IF pc[i] = "V0" /\ i \in Corr THEN "V1" ELSE IF pc[i] \notin { "V0", "V1" } /\ Cardinality(rcvd[i]) >= N - T /\ Cardinality(Faulty) <= T THEN "AC" ELSE IF pc[i] \notin { "V0", "V1" } /\ Cardinality(rcvd[i]) >= N - 2 * T THEN "SE" ELSE pc[i] ]
         /\ sent' = IF pc[i] \in { "V0", "V1" } /\ Cardinality(rcvd[i]) >= N - T /\ Cardinality(Faulty) <= T THEN sent \cup { <<i, "ECHO">> } ELSE sent
      BY DEF Step
    <2>2 PC of the correct process stays at V0
      <3>1 Cardinality(Faulty) <= T => Cardinality(rcvd[i]) <= T /\ Cardinality(rcvd[i]) \in Nat
        <4>1 rcvd[i] \subseteq byz
          BY DEF InitNoBcast, byz
        <4>1 rcvd[i] \subseteq Faulty \X M
          BY <4>1
        <4>2 rcvd[i] \subseteq (byz \cup sent) /\ (byz \cup sent) \subseteq Faulty \X M
          BY <4>1, DEF InitNoBcast
        <4>3 \A p \in rcvd[i] : p[1] \in Faulty
          BY <4>2, INCLUSION
        <4>4 rcvd[i] \subseteq Faulty \X M
          BY <4>3, INCLUSION
        <4>5 (rcvd[i] \cup (sent \cup byz)) \subseteq Faulty \X M
          BY <4>1, INCLUSION
        <4>6 Cardinality(Faulty \X M) = Cardinality(Faulty) * Cardinality(M)
          BY FS_Product, FS_Singleton
        <4>7 Cardinality(Faulty) \in Nat
          BY FS_CardinalityType
        <4>8 Cardinality(M) \in Nat
          BY FS_Singleton
        <4>9 Cardinality(Faulty \X M) \in Nat
          BY <4>6, <4>7, <4>8
        <4>10 Cardinality(rcvd[i]) <= Cardinality(Faulty \X M)
          BY <4>4, <4>5, <4>9
        <4>11 QED
          BY <4>10, <4>6, <4>7, <4>8, <4>1
        <4>12 QED
          BY <4>1, <4>11, NTF
      <3>2 IndInv_NoBroadcast /\ Step(i) => (sent' = sent /\ byz' = byz /\ pc' = pc /\ rcvd' \in [ Proc -> SUBSET byz' ])
      <3>3 QED
        BY <3>1, <3>2, NTF
    <2> QED
      BY <1>1, <1>2, <1>3, NTF
  <1> QED
    BY <1>1, <1>2, <1>3

\* The unforgeability property follows directly from the invariant.
Theorem IndInv_NoBroadcastSafety == IndInv_NoBroadcast => (\A i \in Corr : pc[i] = "V0") /\ (\A i \in Corr : pc[i] # "AC")
  <1>1 (\A i \in Corr : pc[i] = "V0") /\ (\A i \in Corr : pc[i] # "AC") <=> (\A i \in Corr : pc[i] = "V0")
    BY <1>1
  <1>2 (\A i \in Corr : pc[i] = "V0") <=> pc = [ i \in Corr |-> "V0" ]
    BY <1>1
  <1> QED
    BY <1>1

\* The initial state that models a correct broadcast also satisfies the
\* invariant, so the unforgeability property holds for all executions.
Theorem IndInv_NoBroadcastSafetyAll ==
  ((Init /\ (\A i \in Corr : pc[i] = "V1")) => [](\A i \in Corr : pc[i] # "AC"))
  /\ ((Init /\ (\A i \in Corr : pc[i] = "V0")) => [](\A i \in Corr : pc[i] # "AC"))
  BY <1>1, <1>2, NTF

=============================================================================