---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (to be instantiated by the model checker)
-----------------------------------------------------------------*)
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Interval for sending alive messages (positive integer)
    PredictPoint,  \* Interval for making predictions (positive integer)
    Messages       \* Set of all possible messages

(*-----------------------------------------------------------------
  Message definition
-----------------------------------------------------------------*)
Message == [type : {"alive"}, from : Proc, to : Proc]

ASSUME Messages = Message

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    Suspect,   \* [p \in Proc |-> SUBSET Proc]   – suspicion set of each process
    Timeout,   \* [p \in Proc |-> [q \in Proc |-> Nat]] – timeout intervals
    Counter,   \* [p \in Proc |-> [q \in Proc |-> Nat]] – ticks since last hearing
    Clock,     \* [p \in Proc |-> Nat]                – local clocks
    Channel    \* Set of messages currently in transit

vars == << Suspect, Timeout, Counter, Clock, Channel >>

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AliveMsg(p, q) == [type |-> "alive", from |-> p, to |-> q]

SendTimes   == { n \in Nat : n % SendPoint = 0 }
PredictTimes== { n \in Nat : n % PredictPoint = 0 }

IsSend(p) ==
    /\ Clock[p] \in SendTimes
    /\ Clock[p] \notin PredictTimes

IsPredict(p) ==
    /\ Clock[p] \in PredictTimes
    /\ Clock[p] \notin SendTimes

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ Suspect = [p \in Proc |-> {}]
    /\ Timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ Counter = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock   = [p \in Proc |-> 0]
    /\ Channel = {}

(*-----------------------------------------------------------------
  Send action for a process p
-----------------------------------------------------------------*)
Send(p) ==
    /\ IsSend(p)
    /\ \* create alive messages for every other process
       let newMsgs == { AliveMsg(p, q) : q \in Proc \ {p} } in
       /\ Channel' = Channel \cup newMsgs
    /\ \* increment counters for all q ≠ p (unless already timed‑out)
       Counter' = [Counter EXCEPT ![p] = 
                       [q \in Proc |-> 
                          IF q = p THEN Counter[p][q]
                          ELSE Counter[p][q] + 1]]
    /\ \* advance local clock, wrap around if exceeds all thresholds
       Clock'   = [Clock EXCEPT ![p] = 
                       (Clock[p] + 1) % (SendPoint + PredictPoint + MaxTimeout(p))]
    /\ UNCHANGED << Suspect, Timeout, Channel \ {AliveMsg(_, _)} >>
    /\ UNCHANGED << Suspect, Timeout, Channel >>
    /\ UNCHANGED << Suspect, Timeout, Channel >>

(*-----------------------------------------------------------------
  Predict action for a process p
-----------------------------------------------------------------*)
Predict(p) ==
    /\ IsPredict(p)
    /\ \* add to suspicion any process whose counter exceeds its timeout
       let newSus == { q \in Proc \ {p} : Counter[p][q] > Timeout[p][q] } in
       Suspect' = [Suspect EXCEPT ![p] = Suspect[p] \cup newSus]
    /\ \* increment all counters (including those just added to suspicion)
       Counter' = [Counter EXCEPT ![p] = 
                       [q \in Proc |-> Counter[p][q] + 1]]
    /\ \* advance clock
       Clock'   = [Clock EXCEPT ![p] = 
                       (Clock[p] + 1) % (SendPoint + PredictPoint + MaxTimeout(p))]
    /\ UNCHANGED << Timeout, Channel >>

(*-----------------------------------------------------------------
  Receive action for a process p
-----------------------------------------------------------------*)
Receive(p) ==
    /\ ~IsSend(p) /\ ~IsPredict(p)
    /\ \* nondeterministically pick any subset of messages addressed to p
       let recv == { m \in Channel : m.to = p } in
       \E r \subseteq recv :
         /\ \* reset counters and clear suspicion for senders of received alive msgs
            Counter' = [Counter EXCEPT ![p] = 
                           [q \in Proc |-> 
                              IF q \in { m.from : m \in r } THEN 0
                              ELSE Counter[p][q] + 1]]
            /\ Suspect' = [Suspect EXCEPT ![p] = 
                             Suspect[p] \ { m.from : m \in r }]
         /\ \* adaptive timeout increase for any suspected sender whose
               message was received
            Timeout' = [Timeout EXCEPT ![p] = 
                           [q \in Proc |-> 
                              IF q \in (Suspect[p] \cap { m.from : m \in r })
                                 THEN Timeout[p][q] + 1
                                 ELSE Timeout[p][q]]]
         /\ \* remove the received messages from the channel
            Channel' = Channel \ r
         /\ \* advance clock (wrap around)
            Clock'   = [Clock EXCEPT ![p] = 
                           (Clock[p] + 1) % (SendPoint + PredictPoint + MaxTimeout(p))]
         /\ UNCHANGED << Suspect, Timeout, Counter, Clock >> \* other processes unchanged

(*-----------------------------------------------------------------
  Helper to compute a bound for wrap‑around (any sufficiently large
  number works; we use the maximum timeout seen by p plus the two
  intervals)
-----------------------------------------------------------------*)
MaxTimeout(p) ==
    Max({ Timeout[p][q] : q \in Proc }) + SendPoint + PredictPoint

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

SPECIFICATION == Spec

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ Suspect \in [Proc -> SUBSET Proc]
    /\ Timeout \in [Proc -> [Proc -> Nat]]
    /\ Counter \in [Proc -> [Proc -> Nat]]
    /\ Clock   \in [Proc -> Nat]
    /\ Channel \subseteq Messages
    /\ \A m \in Channel :
          /\ m.type = "alive"
          /\ m.from \in Proc
          /\ m.to   \in Proc
    /\ \A p \in Proc : Timeout[p][p] = 0

INVARIANTS == TypeOK

(*-----------------------------------------------------------------
  Additional (empty) property placeholder
-----------------------------------------------------------------*)
PROPERTIES == TRUE

====