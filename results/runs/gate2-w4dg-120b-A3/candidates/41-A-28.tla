---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,          \* the processes in the system
  d0,            \* the default timeout interval
  SendPoint,     \* the clock value at which a process sends alive messages
  PredictPoint,  \* the clock value at which a process evaluates its suspicion list
  Messages       \* the type of alive messages that can be sent

ASSUME /\ SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # PredictPoint
       /\ d0 \in Nat /\ d0 > 0

Message == Messages
From == [proc : Proc, to : Proc]
Process == [suspicion : SUBSET Proc,
            timeout : [Proc -> Nat],
            lastHeard : [Proc -> Nat],
            clock : Nat,
            outgoing : SUBSET Message]

VARIABLES data

vars == <<data>>

\* Initial state: nobody suspects anybody, everything else at its defaults.
Init ==
  /\ data \in [Proc -> Process]
  /\ \A p \in Proc :
       /\ data[p].suspicion = {}
       /\ data[p].timeout = [q \in Proc |-> d0]
       /\ data[p].lastHeard = [q \in Proc |-> 0]
       /\ data[p].clock = 0
       /\ data[p].outgoing = {}

\* Send alive messages, available only on the send clock tick.
SendMsg ==
  /\ \E p \in Proc :
       /\ data[p].clock = SendPoint
       /\ data[p].clock # PredictPoint
       /\ data' = [data EXCEPT ![p] = [suspicion |-> data[p].suspicion,
                                        timeout |-> data[p].timeout,
                                        lastHeard |-> [q \in Proc |->
                                          IF q = p \/ data[p].lastHeard[q] >= data[p].timeout[q]
                                          THEN data[p].lastHeard[q]
                                          ELSE data[p].lastHeard[q] + 1],
                                        clock |-> data[p].clock + 1,
                                        outgoing |-> { m \in Message : m.to \in Proc \ {p} }]]
  /\ UNCHANGED data

\* Evaluate the suspicion list on the predict clock tick.
Predict ==
  /\ \E p \in Proc :
       /\ data[p].clock = PredictPoint
       /\ data[p].clock # SendPoint
       /\ data' = [data EXCEPT ![p] = [suspicion |-> { q \in Proc : q # p /\ data[p].lastHeard[q] >= data[p].timeout[q] },
                                        timeout |-> data[p].timeout,
                                        lastHeard |-> [q \in Proc |->
                                          IF q = p \/ data[p].lastHeard[q] >= data[p].timeout[q]
                                          THEN data[p].lastHeard[q]
                                          ELSE data[p].lastHeard[q] + 1],
                                        clock |-> data[p].clock + 1,
                                        outgoing |-> data[p].outgoing]]
  /\ UNCHANGED data

\* Receive incoming messages and adapt timeout intervals when needed.
Receive ==
  /\ \E p \in Proc :
       /\ data[p].clock # SendPoint
       /\ data[p].clock # PredictPoint
       /\ data' = [data EXCEPT ![p] = [suspicion |-> IF data[p].outgoing = {} THEN {} ELSE data[p].suspicion,
                                        timeout |-> [q \in Proc |->
                                          IF \E m \in data[p].outgoing : m.from = q
                                          THEN data[p].timeout[q] + 1
                                          ELSE data[p].timeout[q]],
                                        lastHeard |-> [q \in Proc |->
                                          IF \E m \in data[p].outgoing : m.from = q
                                          THEN 0
                                          ELSE data[p].lastHeard[q]],
                                        clock |-> IF data[p].clock + 1 > SendPoint
                                                    /\ data[p].clock + 1 > PredictPoint
                                                    /\ \A q \in Proc :
                                                         data[p].clock + 1 > data[p].timeout[q]
                                                  THEN 0
                                                  ELSE data[p].clock + 1,
                                        outgoing |-> {}]]
  /\ UNCHANGED data

Next == SendMsg \/ Predict \/ Receive

Spec == Init /\ [][Next]_vars

\* SAFETY PROPERTY: lastHeard counters and timeout intervals are always integers,
\* the suspicion set is always a subset of Proc, and outgoing messages are messages.
TypeOK ==
  /\ \A p \in Proc : data[p].lastHeard \in [Proc -> Nat]
  /\ \A p \in Proc : data[p].timeout \in [Proc -> Nat]
  /\ \A p \in Proc : data[p].suspicion \subseteq Proc
  /\ \A p \in Proc : data[p].outgoing \subseteq Message

====