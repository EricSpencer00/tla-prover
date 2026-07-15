---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,            \* Set of processes
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Send interval (positive integer)
    PredictPoint,    \* Predict interval (positive integer)
    Messages         \* Set of all possible alive messages

(* ------------------------------------------------------------------------ *)
(* Derived sets and helper definitions                                      *)
(* ------------------------------------------------------------------------ *)

MsgFrom(p) == { m \in Messages : m["from"] = p }

(* A simple representation of an alive message: a record with a sender field. *)
AliveMessage(p) == [type |-> "Alive", from |-> p]

(* ------------------------------------------------------------------------ *)
(* Variables                                                                *)
(* ------------------------------------------------------------------------ *)

VARIABLES
    suspicion,   \* [p \in Proc -> SUBSET Proc] : processes p currently suspects
\*   timeout,    \* [p \in Proc -> [q \in Proc -> Nat]] : timeout interval for each pair
\*   lastHeard,  \* [p \in Proc -> [q \in Proc -> Nat]] : ticks since p last heard from q
\*   lc,         \* [p \in Proc -> Nat]               : local clock of each process
\*   outbox,     \* [p \in Proc -> SUBSET Messages]   : messages p intends to send
    timeout, 
    lastHeard, 
    lc, 
    outbox

(* ------------------------------------------------------------------------ *)
(* Initialization                                                            *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ lc        = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(* ------------------------------------------------------------------------ *)
(* Helper predicates                                                         *)
(* ------------------------------------------------------------------------ *)

IsSendStep(p) == /\ lc[p] % SendPoint = 0
                 /\ lc[p] % PredictPoint # 0

IsPredictStep(p) == /\ lc[p] % PredictPoint = 0
                    /\ lc[p] % SendPoint # 0

EitherSendOrPredict(p) == IsSendStep(p) \/ IsPredictStep(p)

(* ------------------------------------------------------------------------ *)
(* Actions for a single process                                             *)
(* ------------------------------------------------------------------------ *)

SendAlive(p) ==
    /\ IsSendStep(p)
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMessage(q) : q \in Proc \ {p} }]
    /\ (\A q \in Proc \ {p} :
            IF lastHeard[p][q] + 1 >= timeout[p][q]
            THEN TRUE
            ELSE lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1])
    /\ lc' = [lc EXCEPT ![p] = lc[p] + 1]
    /\ UNCHANGED << suspicion, timeout, lastHeard >>

Predict(p) ==
    /\ IsPredictStep(p)
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
                     { q \in Proc \ {p} :
                         lastHeard[p][q] + 1 >= timeout[p][q] }]
    /\ lc' = [lc EXCEPT ![p] = lc[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1
                                          \* for all q (including suspected ones) *)
    /\ UNCHANGED << timeout, outbox >>

Receive(p) ==
    /\ ~EitherSendOrPredict(p)
    /\ \A m \in outbox[p] :
          /\ m["type"] = "Alive"
          /\ m["from"] \in Proc
    /\ (* Process all incoming alive messages *)
       /\ (\A q \in Proc :
              IF q # p /\ AliveMessage(q) \in outbox[p]
              THEN /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
                   /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q}]
                   /\ timeout'   = [timeout EXCEPT ![p][q] = timeout[p][q] + 1]
              ELSE UNCHANGED << lastHeard, suspicion, timeout >>)
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ lc' = [lc EXCEPT ![p] = lc[p] + 1]
    /\ UNCHANGED << suspicion, timeout, lastHeard >>

ClockReset(p) ==
    /\ lc[p] > Max(SendPoint, PredictPoint, d0, timeout[p][p]) (* safe upper bound *)
    /\ lc' = [lc EXCEPT ![p] = 0]
    /\ UNCHANGED << suspicion, timeout, lastHeard, outbox >>

ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ ClockReset(p)

(* ------------------------------------------------------------------------ *)
(* Global next-state relation                                                *)
(* ------------------------------------------------------------------------ *)

Next == \E p \in Proc : ProcStep(p)

(* ------------------------------------------------------------------------ *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, lc, outbox>>

(* ------------------------------------------------------------------------ *)
(* Type invariant (the only invariant required by the .cfg)                *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ lc        \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

=================================