---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
          NaturalsInduction, SequenceTheorems, TLAPS
CONSTANTS N, T, F

\* We model a one-round broadcast algorithm with Byzantine faults. The
\* 2nd and 3rd if-then expressions in Fig. 7 of the paper are swapped (the
\* accept-and-broadcast case now comes before the broadcast-until-accept
\* case) so that the number of messages received is monotone and the
\* Cardinality constraint in "UponAcceptNotSentBefore" is a syntactically
\* non-trivial arithmetic monotone (a conjunction that grows when the
\* predecessor state grows). This is the only change to the model.

VARIABLES Corr, Faulty, pc, rcvd, sent

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3*T /\ T >= F /\ F >= 0

Proc == 1..N
M == { "ECHO" }
ByzMsgs == Faulty \X M

vars == << Corr, Faulty, pc, rcvd, sent >>

Init == /\ sent = {}
        /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
        /\ rcvd = [ i \in Proc |-> {} ]
        /\ Corr \in SUBSET Proc
        /\ Cardinality(Corr) = N - F
        /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

TypeOK == /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
          /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
          /\ sent \subseteq Proc \X M
          /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

FCConstraints == /\ Corr \cup Faulty = Proc
                  /\ Faulty = Proc \ Corr
                  /\ Cardinality(Corr) >= N - T
                  /\ Cardinality(Faulty) <= T
                  /\ ByzMsgs \subseteq Proc \X M
                  /\ IsFiniteSet(ByzMsgs)
                  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

\* A correct process receives any subset of the messages sent by other
\* correct processes plus any subset of the Byzantine processes' messages.
Receive(p, byz?) ==
  \E m \in SUBSET (sent \cup (IF byz? THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = p THEN rcvd[i] \cup m ELSE rcvd[i] ]

ReceiveFromCorrect(p) == Receive(p, FALSE)

UponV1(p) == /\ pc[p] = "V1"
             /\ pc' = [ pc EXCEPT ![p] = "SE" ]
             /\ sent' = sent \cup {<<p,"ECHO">>}
             /\ UNCHANGED << Corr, Faulty >>

\* The swapped case: a process accepts and broadcasts as soon as it can.
UponAcceptNotSentBefore(p) ==
  /\ pc[p] \in {"V0","V1"}
  /\ Cardinality(rcvd[p]) >= N - T
  /\ pc' = [ pc EXCEPT ![p] = "AC" ]
  /\ sent' = sent \cup {<<p,"ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponNonFaulty(p) ==
  /\ pc[p] \notin {"V0","V1"}
  /\ Cardinality(rcvd[p]) >= N - 2*T
  /\ Cardinality(rcvd[p]) < N - T
  /\ pc' = [ pc EXCEPT ![p] = "SE" ]
  /\ sent' = sent \cup {<<p,"ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(p) ==
  /\ pc[p] = "SE"
  /\ Cardinality(rcvd[p]) >= N - T
  /\ pc' = [ pc EXCEPT ![p] = "AC" ]
  /\ UNCHANGED << sent, Corr, Faulty >>

Step(p) ==
  /\ (ReceiveFromCorrect(p) \/ ReceiveFromCorrect(p) \/ UponV1(p) \/ UponNonFaulty(p)
        \/ UponAcceptNotSentBefore(p) \/ UponAcceptSentBefore(p))
  /\ UNCHANGED << Corr, Faulty >>

Next == \E p \in Corr : Step(p) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(\E p \in Corr : ReceiveFromCorrect(p))

SpecNoBcast == InitNoBcast /\ [][Next]_vars

\* Unforgeability: if no correct process broadcast, no correct process
\* accepts. As a first-order formula it simplifies to "no correct process
\* ever accepts", which is entailed by the inductive invariant below.
Unforg == (\A i \in Proc : i \in Corr => (pc[i] # "AC"))

IndInv_Unforg == TypeOK /\ FCConstraints /\ sent = {} /\ pc = [ i \in Proc |-> "V0" ]

THEOREM InitNoBcastInv == InitNoBcast => IndInv_Unforg
  BY DEF InitNoBcast, IndInv_Unforg

THEOREM IndStep ==
  IndInv_Unforg /\ [Next]_vars => IndInv_Unforg'
  BY DEF Next, IndInv_Unforg, Receive, UponV1, UponNonFaulty,
        UponAcceptNotSentBefore, UponAcceptSentBefore

THEOREM IndInvImpliesUnforg == IndInv_Unforg => Unforg
  BY DEF IndInv_Unforg, Unforg

THEOREM SpecImpliesUnforg == SpecNoBcast => []Unforg
  BY InitNoBcastInv, IndStep, IndInvImpliesUnforg, PTL

====