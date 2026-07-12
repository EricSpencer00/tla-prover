---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES Susp, Timeout, Heard, Clock, Out

(* ------------------------------------------------------------------- *)
(* Helper definitions *)
\* The set of processes from which a process can receive messages
Other(p) == Proc \ {p}

\* Sequential ordering of alive messages (p sends to q)
AliveMsg(p, q) == <<p, q>>

\* Maximum clock value used for resetting local clocks
MaxClock == Max({SendPoint, PredictPoint}) + Max({d0}) + 1

\* Compute next clock value with reset
NextClock(c) == IF c >= MaxClock THEN 0 ELSE c + 1

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ Susp = [p \in Proc |-> {}]
    /\ Timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
    /\ Heard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
    /\ Clock = [p \in Proc |-> 0]
    /\ Out = [p \in Proc |-> {}]

(* ------------------------------------------------------------------- *)
(* Send alive messages action for process p *)
Send(p) ==
    /\ Clock[p] = SendPoint
    /\ \A q \in Other(p) : AliveMsg(p, q) \in Out[p]'
    /\ Out' = [Out EXCEPT ![p] = Out[p] \cup { AliveMsg(p, q) : q \in Other(p) }]
    /\ Clock' = [Clock EXCEPT ![p] = NextClock(Clock[p])]
    /\ Susp' = Susp
    /\ Timeout' = Timeout
    /\ Heard' = [Heard EXCEPT ![p] = [q \in Other(p) |-> Heard[p][q] + 1]]

(* ------------------------------------------------------------------- *)
(* Predict action for process p *)
Predict(p) ==
    /\ Clock[p] = PredictPoint
    /\ \A q \in Other(p) :
          IF Heard[p][q] > Timeout[p][q] THEN q \in Susp[p]' ELSE q \notin Susp[p]'
    /\ Susp' = [Susp EXCEPT ![p] = { q \in Other(p) : Heard[p][q] > Timeout[p][q] }]
    /\ Timeout' = Timeout
    /\ Heard' = [Heard EXCEPT ![p] = [q \in Other(p) |-> Heard[p][q] + 1]]
    /\ Clock' = [Clock EXCEPT ![p] = NextClock(Clock[p])]
    /\ Out' = Out

(* ------------------------------------------------------------------- *)
(* Receive action for process p *)
Receive(p) ==
    /\ Clock[p] # SendPoint
    /\ Clock[p] # PredictPoint
    /\ \E q \in Other(p) : AliveMsg(q, p) \in Out[q]
    /\ Out' = [Out EXCEPT ![q] = Out[q] \ { AliveMsg(q, p) } : q \in Other(p)]
    /\ Susp' = [Susp EXCEPT ![p] =
                   IF AliveMsg(q, p) \in Out[q] THEN Susp[p] \ {q} ELSE Susp[p] ]
    /\ Timeout' = [Timeout EXCEPT ![p] =
                     IF AliveMsg(q, p) \in Out[q] THEN Timeout[p][q] + 1 ELSE Timeout[p][q] ]
    /\ Heard' = [Heard EXCEPT ![p] =
                    IF AliveMsg(q, p) \in Out[q] THEN 0 ELSE Heard[p][q] ]
    /\ Clock' = Clock

(* ------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \E p \in Proc :
        (Send(p)
         \/ Predict(p)
         \/ Receive(p))

(* ------------------------------------------------------------------- *)
(* Specifications for TLC *)
Spec == Init /\ [][Next]_<<Susp, Timeout, Heard, Clock, Out>>

(* ------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
    /\ Susp \in [Proc -> SUBSET Proc]
    /\ Timeout \in [Proc -> [PROC -> Nat]]
    /\ Heard \in [Proc -> [PROC -> Nat]]
    /\ Clock \in [Proc -> Nat]
    /\ Out \in [Proc -> SUBSET Messages]

====