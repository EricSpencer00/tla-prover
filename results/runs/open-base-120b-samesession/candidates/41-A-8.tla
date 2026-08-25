---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(*  Constants that must be supplied by the model checker configuration   *)
(***************************************************************************)
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (natural number)
    SendPoint,     \* Periodicity of sending alive messages (positive integer)
    PredictPoint,  \* Periodicity of making predictions (positive integer)
    Messages       \* Set of all possible messages

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES
    Suspects,   \* [p \in Proc |-> SUBSET Proc]   -- suspicion set of each process
    Timeout,    \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout per pair
    Last,       \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive from q
    Clock,      \* [p \in Proc |-> Nat]          -- local clock of each process
    Out         \* [p \in Proc |-> SUBSET Messages]   -- messages a process wants to send

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)
MaxTimeout(p) ==
    Max({SendPoint, PredictPoint} \cup { Timeout[p][q] : q \in Proc })

IncClock(p) ==
    IF Clock[p] + 1 > MaxTimeout(p) THEN 0 ELSE Clock[p] + 1

(*  The set of alive messages a process p creates when it sends *)
AliveMsgs(p) ==
    { [sender |-> p,
       receiver |-> q,
       type    |-> "alive"] : q \in Proc \ {p} }

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init ==
    /\ Suspects = [p \in Proc |-> {}]
    /\ Timeout  = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ Last     = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock    = [p \in Proc |-> 0]
    /\ Out      = [p \in Proc |-> {}]

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

SendAlive(p) ==
    /\ p \in Proc
    /\ Clock[p] % SendPoint = 0
    /\ Clock[p] % PredictPoint # 0
    /\ Out' = [Out EXCEPT ![p] = AliveMsgs(p)]
    /\ Clock' = [Clock EXCEPT ![p] = IncClock(p)]
    /\ Last' = [Last EXCEPT ![p] = 
                [q \in Proc |-> IF q # p THEN Last[p][q] + 1 ELSE @]]
    /\ UNCHANGED << Suspects, Timeout >>

Predict(p) ==
    /\ p \in Proc
    /\ Clock[p] % PredictPoint = 0
    /\ Clock[p] % SendPoint # 0
    /\ let newSuspects == { q \in Proc \ {p} : Last[p][q] > Timeout[p][q] } in
       Suspects' = [Suspects EXCEPT ![p] = Suspects[p] \cup newSuspects]
    /\ Clock' = [Clock EXCEPT ![p] = IncClock(p)]
    /\ Last' = [Last EXCEPT ![p] = 
                [q \in Proc |-> IF q # p THEN Last[p][q] + 1 ELSE @]]
    /\ UNCHANGED << Timeout, Out >>

(*  Receive action: nondeterministically receive a subset of alive messages *)
Receive(p) ==
    /\ p \in Proc
    /\ (Clock[p] % SendPoint # 0) /\ (Clock[p] % PredictPoint # 0)
    /\ \E R \subseteq Proc \ {p} :
        /\ (* R is the set of processes from which p receives an alive message this step *)
        (* Update last‑heard counters *)
        Last' = [Last EXCEPT ![p] =
                    [q \in Proc |-> 
                        IF q \in R THEN 0
                        ELSE IF q # p THEN Last[p][q] + 1
                        ELSE @]]
        /\ (* Remove received processes from the suspicion set *)
        Suspects' = [Suspects EXCEPT ![p] = Suspects[p] \ R]
        /\ (* Adaptive timeout: increase timeout for those that were suspected
              but whose alive message was received *)
        Timeout' = [Timeout EXCEPT ![p] =
                    [q \in Proc |-> 
                        IF q \in R /\ q \in Suspects[p] THEN Timeout[p][q] + 1
                        ELSE @]]
        /\ Clock' = [Clock EXCEPT ![p] = IncClock(p)]
        /\ Out' = Out
    /\ UNCHANGED << >>

(***************************************************************************)
(*  Next-state relation                                                   *)
(***************************************************************************)
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [] [Next]_<< Suspects, Timeout, Last, Clock, Out >>

(***************************************************************************)
(*  Type invariant                                                        *)
(***************************************************************************)
TypeOK ==
    /\ Suspects \in [Proc -> SUBSET Proc]
    /\ Timeout  \in [Proc -> [Proc -> Nat]]
    /\ Last     \in [Proc -> [Proc -> Nat]]
    /\ Clock    \in [Proc -> Nat]
    /\ Out      \in [Proc -> SUBSET Messages]

(***************************************************************************)
(*  The set of invariants that the model checker must check                *)
(***************************************************************************)
INVARIANT TypeOK

=============================================================================