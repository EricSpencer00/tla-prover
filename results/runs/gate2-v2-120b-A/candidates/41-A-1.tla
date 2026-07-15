---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,          \* Set of all processes
    d0,            \* Default timeout value
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval
    Messages       \* Set of all possible alive messages (defined below)

(* ------------------------------------------------------------------------ *)
(* Helper definitions *)
(* ------------------------------------------------------------------------ *)

Message == [src : Proc, dst : Proc]

(* ------------------------------------------------------------------------ *)
(* State variables *)
(* ------------------------------------------------------------------------ *)

VARIABLES
    sus,          \* Suspected set for each process: [p \in Proc |-> SUBSET Proc]
    timeout,      \* Adaptive timeout for each process-pair: [p \in Proc |-> [q \in Proc |-> Nat]]
    last,         \* Ticks since last heard from each process-pair: [p \in Proc |-> [q \in Proc |-> Nat]]
    clock,        \* Local clock for each process: [p \in Proc |-> Nat]
    out           \* Outgoing messages for each process: [p \in Proc |-> SUBSET Message]

(* ------------------------------------------------------------------------ *)
(* Initialization *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ out = [p \in Proc |-> {}]

(* ------------------------------------------------------------------------ *)
(* Send alive action *)
(* ------------------------------------------------------------------------ *)

Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { [src |-> p, dst |-> q] : q \in Proc \ {p} }]
    /\ sus' = sus
    /\ timeout' = timeout
    /\ last' = [last EXCEPT
                ![p][q] = IF q # p THEN last[p][q] + 1 ELSE last[p][q]
                \A q \in Proc \ {p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<sus, timeout, last, out>>

(* ------------------------------------------------------------------------ *)
(* Predict action *)
(* ------------------------------------------------------------------------ *)

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ sus' = [sus EXCEPT
                ![p] = { q \in Proc \ {p} :
                         last[p][q] > timeout[p][q] } \cup sus[p]]
    /\ out' = out
    /\ timeout' = timeout
    /\ last' = [last EXCEPT
                ![p][q] = IF q # p THEN last[p][q] + 1 ELSE last[p][q]
                \A q \in Proc \ {p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<sus, out, timeout, last>>

(* ------------------------------------------------------------------------ *)
(* Receive action *)
(* ------------------------------------------------------------------------ *)

Receive(p) ==
    /\ LET incoming == { m \in out[q] : m.dst = p } IN
       /\ sus' = [sus EXCEPT
                  ![p] = sus[p] \ { src |-> m \in incoming @ m.src }]
    /\ timeout' = [timeout EXCEPT
                    ![p][q] = IF
                                 (\E m \in incoming : m.src = q) /\ q \in sus[p]
                               THEN timeout[p][q] + 1
                               ELSE timeout[p][q]
                    \A q \in Proc \ {p}]
    /\ last' = [last EXCEPT
                ![p][q] = IF (\E m \in incoming : m.src = q) THEN 0 ELSE last[p][q]
                \A q \in Proc \ {p}]
    /\ out' = [out EXCEPT ![p] = {}]   \* messages are consumed after reception
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > Max(SendPoint, PredictPoint, d0 + 1) THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED <<sus, timeout, last, out>>

(* ------------------------------------------------------------------------ *)
(* Next-state relation *)
(* ------------------------------------------------------------------------ *)

Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(* ------------------------------------------------------------------------ *)
(* Specification *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_<<sus, timeout, last, clock, out>>

(* ------------------------------------------------------------------------ *)
(* Type correctness invariant (TypeOK) *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Message]

====