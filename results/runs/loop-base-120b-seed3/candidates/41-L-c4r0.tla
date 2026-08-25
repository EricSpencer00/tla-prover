---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES Suspect, Timeout, Last, Clock, Out

(* Message record type – alive messages only *)
Message == [type : {"alive"}, src : Proc, dst : Proc]

(* All messages currently in the system, gathered from the outgoing sets *)
AllMsgs == UNION { Out[p] : p \in Proc }

(* Initial state *)
Init ==
    /\ Suspect = [p \in Proc |-> {}]
    /\ Timeout = [p \in Proc |-> [q \in Proc |-> IF p # q THEN d0 ELSE 0]]
    /\ Last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock   = [p \in Proc |-> 0]
    /\ Out     = [p \in Proc |-> {}]

(* Send alive messages *)
Send(p) ==
    /\ (Clock[p] % SendPoint) = 0
    /\ (Clock[p] % PredictPoint) # 0
    /\ Out' = [Out EXCEPT ![p] = { [type |-> "alive", src |-> p, dst |-> q] : q \in Proc \ {p} }]
    /\ Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ Last' = [Last EXCEPT ![p][q] = @ + 1]
    /\ Suspect' = Suspect
    /\ Timeout' = Timeout

(* Make predictions about crashed processes *)
Predict(p) ==
    /\ (Clock[p] % PredictPoint) = 0
    /\ (Clock[p] % SendPoint) # 0
    /\ LET newSus == { q \in Proc \ {p} : Last[p][q] > Timeout[p][q] } IN
          Suspect' = [Suspect EXCEPT ![p] = Suspect[p] \cup newSus]
    /\ Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ Last' = [Last EXCEPT ![p][q] = @ + 1]
    /\ Timeout' = Timeout
    /\ Out' = Out

(* Receive incoming alive messages *)
Receive(p) ==
    /\ (Clock[p] % SendPoint) # 0
    /\ (Clock[p] % PredictPoint) # 0
    /\ LET msgsToP == { m \in AllMsgs : m.dst = p } IN
       \E R \subseteq msgsToP :
          /\ Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
          /\ Last' = [Last EXCEPT ![p][q] = IF q \in { m.src : m \in R } THEN 0 ELSE @ + 1]
          /\ Suspect' = [Suspect EXCEPT ![p] = Suspect[p] \ { m.src : m \in R }]
          /\ Timeout' = [Timeout EXCEPT ![p][q] = IF q \in { m.src : m \in R } /\ q \in Suspect[p] THEN @ + 1 ELSE @]
          /\ Out' = Out

(* Next-state relation *)
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

(* Full specification *)
Spec == Init /\ [][Next]_<<Suspect, Timeout, Last, Clock, Out>>

(* Type invariant *)
TypeOK ==
    /\ Suspect \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : Suspect[p] \subseteq Proc \ {p}
    /\ Timeout \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : (p # q) => Timeout[p][q] \in Nat
    /\ Last \in [Proc -> [Proc -> Nat]]
    /\ Clock \in [Proc -> Nat]
    /\ Out \in [Proc -> SUBSET Messages]

(* Assumptions on the intervals *)
ASSUME SendPoint > 0
ASSUME PredictPoint > 0
ASSUME (SendPoint % PredictPoint) # 0
ASSUME (PredictPoint % SendPoint) # 0

====