---------------------------- MODULE EPFailureDetector ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    d0,         \* default timeout interval, a natural number
    SendPoint, \* interval at which a process sends alive messages (never a multiple of PredictPoint)
    PredictPoint, \* interval at which a process evaluates its suspicion list (never a multiple of SendPoint)
    Proc,       \* the set of all processes
    Messages    \* the set of all alive messages, each with a sender and a recipient

ASSUME /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ SendPoint # PredictPoint
       /\ d0 \in Nat /\ d0 >= 1
       /\ \A m \in Messages : m.sender \in Proc /\ m.recipient \in Proc

VARIABLES
    suspect,    \* [Proc -> SUBSET Proc] : which processes a given process suspects of having crashed
    timeout,    \* [Proc -> [Proc -> Nat]] : adaptive timeout interval per target process
    lastHeard,  \* [Proc -> [Proc -> Nat]] : clock ticks since a given process last heard from each target
    myclock,    \* [Proc -> Nat] : local clock per process
    outgoing    \* [Proc -> SUBSET Messages] : messages each process wants to send

vars == <<suspect, timeout, lastHeard, myclock, outgoing>>

MaxClock == 2 * (SendPoint + PredictPoint + d0)

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ myclock \in [Proc -> Nat]
    /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ myclock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

\* Send alive messages; not simultaneously enabled with Predict because SendPoint # PredictPoint
Send(p) ==
    /\ myclock[p] % SendPoint = 0
    /\ myclock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.sender = p}]
    /\ myclock' = [myclock EXCEPT ![p] = myclock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                          IF q \in outgoing[p] /\ lastHeard[p][q] < timeout[p][q]
                          THEN lastHeard[p][q] + 1
                          ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspect, timeout>>

\* Evaluate the suspicion list based on the adaptive timeout
Predict(p) ==
    /\ myclock[p] % PredictPoint = 0
    /\ myclock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
                      {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ myclock' = [myclock EXCEPT ![p] = myclock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                          IF lastHeard[p][q] < timeout[p][q]
                          THEN lastHeard[p][q] + 1
                          ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<timeout, outgoing>>

\* Receive incoming messages and adapt timeout if a suspected process turns out to be correct
Receive(p) ==
    /\ myclock[p] % SendPoint # 0
    /\ myclock[p] % PredictPoint # 0
    /\ \E m \in Messages :
         /\ m.recipient = p
         /\ lastHeard' = [lastHeard EXCEPT ![p][m.sender] = 0]
         /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.sender}]
         /\ timeout' = IF m.sender \in suspect[p]
                        THEN [timeout EXCEPT ![p][m.sender] = timeout[p][m.sender] + 1]
                        ELSE timeout
    /\ myclock' = [myclock EXCEPT ![p] = IF myclock[p] + 1 > MaxClock THEN 0 ELSE myclock[p] + 1]
    /\ UNCHANGED outgoing

Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Receive("p") /\ Send("p"))
    /\ WF_vars(Predict("p"))

Spec == Spec /\ Spec

=============================================================================