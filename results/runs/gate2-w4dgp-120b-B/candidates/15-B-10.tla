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

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == F \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \times M
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

FCConstraints ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ IsFiniteSet(Corr)
  /\ IsFiniteSet(Faulty)
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

Receive(p, includeByz) ==
  \E newMessages \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup newMessages ]

Downstream(p) == Receive(p, FALSE)

Step(p) ==
  \/ Downstream(p) /\ pc[p] = "V1" /\ pc' = [pc EXCEPT ![p] = "SE"]
                      /\ sent' = sent \cup {<<p, "ECHO">>}
  \/ Downstream(p) /\ pc[p] \notin { "V0", "V1" } /\ Cardinality(rcvd'[p]) >= N - 2 * T
                      /\ Cardinality(rcvd'[p]) < N - T
                      /\ pc' = [pc EXCEPT ![p] = "SE"]
                      /\ sent' = sent \cup {<<p, "ECHO">>}
  \/ Downstream(p) /\ pc[p] \in { "V0", "V1" } /\ Cardinality(rcvd'[p]) >= N - T
                      /\ pc' = [pc EXCEPT ![p] = "AC"]
                      /\ sent' = sent \cup {<<p, "ECHO">>}
  \/ Downstream(p) /\ pc[p] = "SE" /\ Cardinality(rcvd'[p]) >= N - T
                      /\ pc' = [pc EXCEPT ![p] = "AC"]
  \/ UNCHANGED << pc, rcvd, sent, Corr, Faulty >>

Next == (\E p \in Corr: Step(p)) \/ UNCHANGED vars

SpecNoBcast ==
  InitNoBcast /\ [][Next]_vars
  /\ WF_vars(\E p \in Corr: /\ Downstream(p) /\ UNCHANGED <<pc, sent, Corr, Faulty>>)

Unforg == (\A i \in Proc: i \in Corr => (pc[i] # "AC"))

UMFS =
  \A X, Y, Z :
    /\ IsFiniteSet(X) /\ IsFiniteSet(Y) /\ IsFiniteSet(Z)
    /\ X \cup Y = Z
    /\ X = Z \ Y
    => Cardinality(X) = Cardinality(Z) - Cardinality(Y)

FCTypeOK == FCConstraints /\ TypeOK
Inv == (\A i \in Proc: pc[i] = "V0") /\ FCTypeOK
InvSimp == (\A i \in Proc: pc[i] = "V0") /\ TypeOK /\ Corr \subseteq Proc /\ Cardinality(Corr) >= N - T

Inductive == InitNoBcast => Inv /\ (Inv /\ [Next]_vars => Inv') /\ (Inv => Unforg)

====