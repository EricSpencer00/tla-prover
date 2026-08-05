------------------------------ MODULE bcastByz ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast distributed  
   algorithm with Byzantine faults.
  
   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:
  
   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94
                                                             
   A short description of the parameterized model is described in: Gmeiner,   
   Annu, et al. "Tutorial on parameterized model checking of fault-tolerant   
   distributed algorithms." International School on Formal Methods for the  
   Design of Computer, Communication and Software Systems. Springer  
   International Publishing, 2014.                   
  
   This specification has a TLAPS proof for property Unforgeability: if process p 
   is correct and does not broadcast a message m, then no correct process ever 
   accepts m. The formula InitNoBcast represents that the transmitter does not 
   broadcast any message. So, our goal is to prove the formula
        (InitNoBcast /\ [][Next]_vars) => []Unforg                    
  
   We can use TLC to check two properties (for fixed parameters N, T, and F):
    - Correctness: if a correct process broadcasts, then every correct process accepts,
    - Replay: if a correct process accepts, then every correct process accepts.  
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
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

VARIABLES Corr          (* the correct processes *)
          Faulty        (* the faulty processes *)
                        (* Corr and Faulty are declared as variables since we want to 
                           check all possible cases. After the initial step they are 
                           unchanged. *)
          pc            (* the control state of each process *)
          rcvd          (* the messages received by each process *)
          sent          (* the messages sent by all correct processes *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N          (* all processes, including the faulty ones    *)
M == { "ECHO" }
ByzMsgs == Faulty \X M
                            
vars == << pc, rcvd, sent, Corr, Faulty >>

(* Instead of modeling a broadcaster explicitly, two initial values V0 and V1 at correct
   processes are used to model whether a process has received the INIT message from the
   broadcaster or not, respectively. Then the precondition of correctness can be modeled 
   that all correct processes initially have value V1, while the precondition of unforgeability  
   that all correct processes initially have value V0.
 *)
Init == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr        
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* A correct process can receive all ECHO messages sent by the other correct processes,
   i.e., a subset of sent, and all possible ECHO messages from the Byzantine processes,
   i.e., a subset of ByzMsgs. If includeByz is FALSE, the messages from the Byzantine
   processes are not included.
 *)
Receive(p, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup newMessages ]

ReceiveFromCorrectSender(p) == Receive(p, FALSE)
ReceiveFromAnySender(p)     == Receive(p, TRUE)

(* process p receives an INIT message and sends ECHO to all. *)
UponV1(p) ==
  /\ pc[p] = "V1"
  /\ pc' = [pc EXCEPT ![p] = "SE"]
  /\ sent' = sent \cup { <<p, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* process p receives ECHO messages from at least N - 2T distinct processes and sends
   ECHO to all. (T + 1) is a stricter bound than (2T + 1), and it guarantees 
   unforgeability: a correct process needs at least T + 1 ECHO messages, which is more
   than the number of messages a Byzantine process can send.                  
 *)
UponNonFaulty(p) ==
  /\ pc[p] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[p]) >= N - 2 * T
  /\ Cardinality(rcvd'[p]) < N - T
  /\ pc' = [pc EXCEPT ![p] = "SE"]
  /\ sent' = sent \cup { <<p, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* process p receives ECHO messages from at least N - T distinct processes and accepts
   (it also sends ECHO to all if it has not sent it before).                 *)
UponAcceptNotSentBefore(p) ==
  /\ pc[p] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "AC"]
  /\ sent' = sent \cup { <<p, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* process p sent ECHO messages and receives ECHO messages from at least N - T distinct
   processes -- it accepts.                                         *)
UponAcceptSentBefore(p) ==
  /\ pc[p] = "SE"
  /\ Cardinality(rcvd'[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

(* All possible process steps. *)
Step(p) == 
  /\ ReceiveFromAnySender(p)
  /\ \/ UponV1(p) \/ UponNonFaulty(p) \/ UponAcceptNotSentBefore(p) \/ UponAcceptSentBefore(p)

(* Some correct process does a transition step. *)
Next == 
  \/ \E p \in Corr : Step(p)
  \/ UNCHANGED vars
  
Spec == Init /\ [][Next]_vars
             /\ WF_vars(\E p \in Corr : /\ ReceiveFromCorrectSender(p)
                                   /\ \/ UponV1(p) \/ UponNonFaulty(p) 
                                      \/ UponAcceptNotSentBefore(p) \/ UponAcceptSentBefore(p))
SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* pc = "V0": the initial state when no process received an INIT message. *)
TypeOK == 
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

(* Corr is large enough to outvote the faulty processes in the broadcast. *)
FCConstraints == 
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)
  
(* The unforgeability property. *)
Unforg == (\A i \in Proc : i \in Corr => (pc[i] /= "AC"))

(* An inductive invariant that looks similar to FCConstraints, but also fixes the
   broadcaster to be silent. 
 *)
IndInv_Unforg_NoBcast ==  
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}  
  /\ pc = [ i \in Proc |-> "V0" ]

(* A TLC-friendly shape of IndInv_Unforg_NoBcast (the order of the conjuncts matters). *)
IndInv_Unforg_NoBcast_TLC ==  
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] /= "AC"
  /\ sent = {}  
  /\ rcvd \in [ Proc -> SUBSET ByzMsgs ]

THEOREM FCConstraints_TypeOK_InitNoBcast == 
  InitNoBcast => FCConstraints /\ TypeOK
  BY DEF InitNoBcast, Init, FCConstraints, TypeOK, ByzMsgs, M

THEOREM FCConstraints_TypeOK_Init == 
  Init => FCConstraints /\ TypeOK
  BY DEF Init, FCConstraints, TypeOK, ByzMsgs, M

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==  
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
  BY DEF IndInv_Unforg_NoBcast

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==  
  IndInv_Unforg_NoBcast_TLC => FCConstraints
  BY DEF IndInv_Unforg_NoBcast_TLC, FCConstraints, TypeOK, ByzMsgs, M

THEOREM FCConstraints_TypeOK_Next ==
  FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
  BY  DEF FCConstraints, TypeOK, Next, vars, Step

THEOREM FCConstraints_TypeOK_SpecNoBcast == SpecNoBcast => [](FCConstraints /\ TypeOK)
  BY  PTL DEF SpecNoBcast, FCConstraints, TypeOK

THEOREM Unforg_Step1 == InitNoBcast => IndInv_Unforg_NoBcast
  <1>1 InitNoBcast => FCConstraints /\ TypeOK
    BY FCConstraints_TypeOK_InitNoBcast
  <1>2 InitNoBcast => sent = {}
    OBVIOUS
  <1>3 InitNoBcast => pc = [ i \in Proc |-> "V0" ]
    OBVIOUS    
  <1> QED

THEOREM Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1>1 IndInv_Unforg_NoBcast' =   
          /\ TypeOK'
          /\ FCConstraints'
          /\ sent' = {}
          /\ pc' = [i \in Proc |-> "V0"]                   
      BY  DEF IndInv_Unforg_NoBcast
  
  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
    <2>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => FCConstraints' /\ TypeOK'
      BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
    <2>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => (sent' = {} /\ pc' = [ j \in Proc |-> "V0" ])
      BY DEF IndInv_Unforg_NoBcast, vars 
    <2> QED
      BY <2>1, <2>2 DEF IndInv_Unforg_NoBcast, vars    
  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
    <2>1 CASE UNCHANGED vars
      <3>1 UnchangedStep ==
              /\ UNCHANGED << pc, rcvd, sent, Corr, Faulty >>
              /\ Cardinality(Faulty) <= T
              /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]
              /\ rcvd \in [ Proc -> SUBSET ByzMsgs ]    
      <3>2 IndInv_Unforg_NoBcast /\ UnchangedStep => IndInv_Unforg_NoBcast'
        BY <2>1
      <3>3 QED
        BY <3>1, <3>2     
    <2>2 CASE (\E p \in Corr : Step(p))
      <3>1 CASE (\E p \in Corr : ReceiveFromAnySender(p) /\ UponV1(p))
        <4>1 FCConstraints'
          BY FCConstraints_TypeOK_Next
        <4>2 IndInv_Unforg_NoBcast' =   
                /\ TypeOK'
                /\ FCConstraints'
                /\ sent' = {}
                /\ pc' = [i \in Proc |-> "V0"]
          BY  DEF IndInv_Unforg_NoBcast
        <4>3 Step(p) /\ ReceiveFromAnySender(p) /\ UponV1(p) => IndInv_Unforg_NoBcast'
          <5>1 Cardinality(rcvd'[p]) <= T /\ Cardinality(rcvd'[p]) \in Nat
            <6>1 sent = {}
              OBVIOUS
            <6>2 sent' = sent \cup { <<p, "ECHO">> }
              BY <6>1
            <6>3 rcvd[p] \subseteq sent \cup ByzMsgs
              BY DEF TypeOK
            <6>4 rcvd[p] \subseteq ByzMsgs
              BY <6>3
            <6>5 rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup { <<p, "ECHO">> } ]
              BY <6>2, DEF ReceiveFromAnySender
            <6>6 rcvd'[p] \subseteq ByzMsgs
              BY <6>4, <6>5
            <6>7 Cardinality(Faulty) <= T
              BY DEF FCConstraints
            <6>8 Cardinality(ByzMsgs) = Cardinality(Faulty)
              BY DEF FCConstraints
            <6>9 Cardinality(ByzMsgs) <= T
              BY <6>7, <6>8
            <6>10 Cardinality(rcvd'[p]) <= Cardinality(ByzMsgs)
              <7>1 rcvd'[p] \in SUBSET ByzMsgs
                BY <6>6
              <7>2 rcvd'[p] \subseteq ByzMsgs
                BY <6>6
              <7> QED
                BY <7>1, <7>2, FS_Subset DEF FCConstraints
            <6>11 Cardinality(ByzMsgs) \in Nat
              BY FS_CardinalityType DEF FCConstraints
            <6>12 QED
              BY <6>6, <6>7, <6>9, <6>10, <6>11, NTFRel            
          <4>4 QED
            BY <4>1, <4>2, <4>3
      <3>2 CASE (\E p \in Corr : ReceiveFromAnySender(p) /\ UponNonFaulty(p))
        <4>1 FCConstraints'
          BY FCConstraints_TypeOK_Next
        <4>2 IndInv_Unforg_NoBcast' =   
                /\ TypeOK'
                /\ FCConstraints'
                /\ sent' = {}
                /\ pc' = [i \in Proc |-> "V0"]
          BY  DEF IndInv_Unforg_NoBcast
        <4>3 Step(p) /\ ReceiveFromAnySender(p) /\ UponNonFaulty(p) => IndInv_Unforg_NoBcast'
          <5>1 Cardinality(rcvd'[p]) <= T /\ Cardinality(rcvd'[p]) \in Nat
            <6>1 Cardinality(rcvd'[p]) <= T
              BY <5>1
            <6>2 ~UponNonFaulty(p)
              <7>1 ~UponNonFaulty(p) =
                      \/ pc[p] \in {"V0", "V1"}
                      \/ Cardinality(rcvd'[p]) < N - 2 * T
                      \/ Cardinality(rcvd'[p]) >= N - T
                      \/ pc' = [pc EXCEPT ![p] = "SE"]
                      \/ sent' = sent \cup { <<p, "ECHO">> }
                      \/ UNCHANGED << Corr, Faulty >>
                BY DEF UponNonFaulty
              <7>2 T < N - 2 * T 
                BY NTFRel
              <7>3 Cardinality(rcvd'[p]) \in Nat
                BY <5>1
              <7>4 Cardinality(rcvd'[p]) < N - 2 * T
                BY <6>2, <7>1, <7>2, <7>3, NTFRel
              <7>5 Cardinality(rcvd'[p]) < N - T
                BY <6>2, <7>4, NTFRel
              <7> QED
                BY <7>1, <7>5, NTFRel
            <6> QED
              BY <6>1, <6>2
          <4>4 QED
            BY <4>1, <4>2, <4>3
      <3>3 CASE (\E p \in Corr : ReceiveFromAnySender(p) /\ UponAcceptNotSentBefore(p))
        <4>1 FCConstraints'
          BY FCConstraints_TypeOK_Next
        <4>2 IndInv_Unforg_NoBcast' =   
                /\ TypeOK'
                /\ FCConstraints'
                /\ sent' = {}
                /\ pc' = [i \in Proc |-> "V0"]
          BY  DEF IndInv_Unforg_NoBcast
        <4>3 Step(p) /\ ReceiveFromAnySender(p) /\ UponAcceptNotSentBefore(p) => IndInv_Unforg_NoBcast'
          <5>1 Cardinality(rcvd'[p]) <= T /\ Cardinality(rcvd'[p]) \in Nat
            <6>1 ~UponAcceptNotSentBefore(p)
              <7>1 ~UponAcceptNotSentBefore(p) =
                      \/ pc[p] \notin {"V0", "V1"}
                      \/ Cardinality(rcvd'[p]) < N - T
                      \/ pc' = [pc EXCEPT ![p] = "AC"]
                      \/ sent' = sent \cup { <<p, "ECHO">> }
                      \/ UNCHANGED << Corr, Faulty >>
                BY DEF UponAcceptNotSentBefore
              <7>2 T < N - 2 * T 
                BY NTFRel
              <7>3 Cardinality(rcvd'[p]) \in Nat
                BY <5>1
              <7>4 Cardinality(rcvd'[p]) < N - 2 * T
                <8>1 \E newMessages \in SUBSET ByzMsgs :
                        rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup newMessages ]
                  BY <5>1
                <8>2 rcvd'[p] \subseteq (rcvd[p] \cup ByzMsgs)
                  <9>1 rcvd'[p] \subseteq (rcvd[p] \cup ByzMsgs)
                    BY <8>1
                  <9>2 QED
                    BY <9>1, FS_Subset DEF FCConstraints
                <8>3 QED
                  BY <8>2, <8>3, FS_Subset DEF FCConstraints
                <7>5 QED
                  BY <7>2, <7>3, <7>4, <8>1, <8>2, <8>3, NTFRel
              <7>6 Cardinality(rcvd'[p]) < N - T
                BY <6>1, <7>5, NTFRel
              <7> QED
                BY <7>1, <7>6, <7>7
            <6> QED
              BY <6>1
          <4>4 QED
            BY <4>1, <4>2, <4>3
      <3>4 CASE (\E p \in Corr : ReceiveFromAnySender(p) /\ UponAcceptSentBefore(p))
        <4>1 FCConstraints'
          BY FCConstraints_TypeOK_Next
        <4>2 IndInv_Unforg_NoBcast' =   
                /\ TypeOK'
                /\ FCConstraints'
                /\ sent' = {}
                /\ pc' = [i \in Proc |-> "V0"]
          BY  DEF IndInv_Unforg_NoBcast
        <4>3 Step(p) /\ ReceiveFromAnySender(p) /\ UponAcceptSentBefore(p) => IndInv_Unforg_NoBcast'
          <5>1 Cardinality(rcvd'[p]) <= T /\ Cardinality(rcvd'[p]) \in Nat
            <6>1 ~UponAcceptSentBefore(p)
              <7>1 ~UponAcceptSentBefore(p) =
                      \/ pc[p] # "SE"
                      \/ Cardinality(rcvd'[p]) < N - T
                      \/ pc' = [pc EXCEPT ![p] = "AC"]
                      \/ sent' = sent
                      \/ UNCHANGED << Corr, Faulty >>
                BY DEF UponAcceptSentBefore
              <7>2 T < N - 2 * T 
                BY NTFRel
              <7>3 Cardinality(rcvd'[p]) \in Nat
                BY <5>1
              <7>4 Cardinality(rcvd'[p]) < N - 2 * T
                <8>1 \E newMessages \in SUBSET ByzMsgs :
                        rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup newMessages ]
                  BY <5>1
                <8>2 rcvd'[p] \subseteq (rcvd[p] \cup ByzMsgs)
                  <9>1 rcvd'[p] \subseteq (rcvd[p] \cup ByzMsgs)
                    BY <8>1
                  <9>2 QED
                    BY <9>1, FS_Subset DEF FCConstraints
                <8>3 QED
                  BY <8>2, <8>3, FS_Subset DEF FCConstraints
                <7>5 QED
                  BY <7>2, <7>3, <7>4, <8>1, <8>2, <8>3, NTFRel
              <7>6 Cardinality(rcvd'[p]) < N - T
                BY <6>1, <7>5, NTFRel
              <7> QED
                BY <7>1, <7>6, <7>7
            <6> QED
              BY <6>1
          <4>4 QED
            BY <4>1, <4>2, <4>3
      <3>5 CASE (\E p \in Corr : ReceiveFromAnySender(p) /\ UNCHANGED << pc, sent, Corr, Faulty >>)
        <4>1 FCConstraints'
          BY FCConstraints_TypeOK_Next
        <4>2 IndInv_Unforg_NoBcast' =   
                /\ TypeOK'
                /\ FCConstraints'
                /\ sent' = {}
                /\ pc' = [i \in Proc |-> "V0"]
          BY  DEF IndInv_Unforg_NoBcast
        <4>3 Step(p) /\ ReceiveFromAnySender(p) /\ UNCHANGED << pc, sent, Corr, Faulty >> => IndInv_Unforg_NoBcast'
          <5>1 Cardinality(rcvd'[p]) <= T /\ Cardinality(rcvd'[p]) \in Nat
            <6>1 Cardinality(rcvd'[p]) <= T
              BY <5>1
            <6>2 (\E newMessages \in SUBSET ByzMsgs :
                        rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup newMessages ])
              <7>1 \E newMessages \in SUBSET ByzMsgs :
                      rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup newMessages ]
                BY <5>1
              <7>2 QED
                BY <7>1, FS_Subset DEF FCConstraints
            <6>3 QED
              BY <6>1, <6>2, FS_Subset DEF FCConstraints                                                           
          <5>2 ~AfterStep
            <6>1 ~AfterStep =
                    \/ pc' = [pc EXCEPT ![p] = "SE"]
                    \/ Cardinality(rcvd'[p]) >= N - T
                    \/ pc' = [pc EXCEPT ![p] = "AC"]
                    \/ UNCHANGED << Corr, Faulty >>
                BY DEF Step
            <6>2 T < N - 2 * T 
              BY NTFRel
            <6>3 Cardinality(rcvd'[p]) \in Nat
              BY <5>1
            <6>4 Cardinality(rcvd'[p]) < N - 2 * T
              <7>1 \E newMessages \in SUBSET ByzMsgs :
                      rcvd' = [ i \in Proc |-> IF i # p THEN rcvd[i] ELSE rcvd[p] \cup newMessages ]
                BY <5>1
              <7>2 rcvd'[p] \subseteq (rcvd[p] \cup ByzMsgs)
                <8>1 rcvd'[p] \subseteq (rcvd[p] \cup ByzMsgs)
                  BY <7>1
                <8>2 QED
                  BY <8>1, FS_Subset DEF FCConstraints
              <7>3 QED
                BY <7>2, <7>3, FS_Subset DEF FCConstraints
              <7>4 QED
                BY <7>1, <7>2, <7>3, <7>4, NTFRel
            <6>5 QED
              BY <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2
          <4>4 QED
            BY <4>1, <4>2, <4>3
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2> QED
      BY <2>1, <2>2
  <1> QED
    BY <1>2, <1>3

THEOREM Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
  <1>1 pc = [i \in Proc |-> "V0" ] => \A i \in Proc : pc[i] # "AC"
    OBVIOUS
  <1>2 (TypeOK /\ pc = [i \in Proc |-> "V0" ]) => \A i \in Proc : pc[i] # "AC"
    BY <1>1
  <1>3 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0" ]) => \A i \in Proc : pc[i] # "AC"
    BY <1>2
  <1>4 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0" ] /\ sent = {}) => \A i \in Proc : pc[i] # "AC"    
    BY <1>3
  <1>5 IndInv_Unforg_NoBcast => \A i \in Proc : pc[i] # "AC"
    BY <1>4 DEF IndInv_Unforg_NoBcast 
  <1>6 IndInv_Unforg_NoBcast => \A i \in Proc : i \in Corr => pc[i] # "AC"
    BY  <1>5     
  <1> QED
    BY <1>6 DEF Unforg

THEOREM Unforg_Step4 == SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast
    BY Unforg_Step1 
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'  
    BY Unforg_Step2
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast
    BY <1>1, <1>2, PTL DEF SpecNoBcast
  <1>4 IndInv_Unforg_NoBcast => Unforg
    BY Unforg_Step3
  <1> QED  
    BY <1>3, <1>4, PTL

=============================================================================