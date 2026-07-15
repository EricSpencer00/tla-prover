---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible messages (must include alive messages)

(* ------------------------------------------------------------------------- *)
(* Types *)
(* ------------------------------------------------------------------------- *)

Message == [type : {"alive"}, src : Proc, dst : Proc]

(* ------------------------------------------------------------------------- *)
(* Variables *)
(* ------------------------------------------------------------------------- *)

VARIABLES
    clock,          \* [p \in Proc -> Nat]  local clock of each process
    timeout,        \* [p \in Proc -> [q \in Proc -> Nat]]  timeout interval that p uses for q
    lastHeard,      \* [p \in Proc -> [q \in Proc -> Nat]]  ticks since p last heard from q
    susp,           \* [p \in Proc -> SUBSET Proc]  suspicion set of each process
    outbox,         \* [p \in Proc -> SUBSET Message]  messages p intends to send this step
    inbox           \* [p \in Proc -> SUBSET Message]  messages p receives this step

(* ------------------------------------------------------------------------- *)
(* Helper definitions *)
(* ------------------------------------------------------------------------- *)

AllProcsExcept(p) == { q \in Proc : q # p }

IsSendStep(p) == 
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0

IsPredictStep(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0

IsOtherStep(p) == 
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0

ResetClock(p) == 
    Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc }) + 1

(* ------------------------------------------------------------------------- *)
(* Initialization *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ susp = [p \in Proc |-> {}]
    /\ outbox = [p \in Proc |-> {}]
    /\ inbox = [p \in Proc |-> {}]

(* ------------------------------------------------------------------------- *)
(* Actions *)
(* ------------------------------------------------------------------------- *)

SendAlive(p) ==
    /\ IsSendStep(p)
    /\ outbox' = [outbox EXCEPT ![p] = 
        { [type |-> "alive", src |-> p, dst |-> q] : q \in AllProcsExcept(p) }]
    /\ clock' = [clock EXCEPT ![p] = 
        IF clock[p] + 1 >= ResetClock(p) THEN 0 ELSE clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
        ![p] = [q \in Proc |-> 
            IF q \in AllProcsExcept(p) 
                THEN lastHeard[p][q] + 1 
                ELSE lastHeard[p][q]]]
    /\ UNCHANGED << timeout, susp, inbox >>

Predict(p) ==
    /\ IsPredictStep(p)
    /\ susp' = [susp EXCEPT ![p] = 
        { q \in AllProcsExcept(p) : 
            (q \in susp[p]) \/ (lastHeard[p][q] > timeout[p][q]) }]
    /\ clock' = [clock EXCEPT ![p] = 
        IF clock[p] + 1 >= ResetClock(p) THEN 0 ELSE clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
        ![p] = [q \in Proc |-> lastHeard[p][q] + 1]]
    /\ UNCHANGED << timeout, outbox, inbox >>

Receive(p) ==
    /\ IsOtherStep(p)
    /\ \A m \in inbox[p] :
          m.type = "alive" /\ m.dst = p
    /\ \* Reset lastHeard for senders and remove them from suspicion
       lastHeard' = [lastHeard EXCEPT 
        ![p] = [q \in Proc |-> 
            IF \E m \in inbox[p] : m.type = "alive" /\ m.src = q 
                THEN 0 
                ELSE lastHeard[p][q] + 1]]
    /\ susp' = [susp EXCEPT 
        ![p] = 
          { q \in susp[p] : 
                \A m \in inbox[p] : 
                    ~(m.type = "alive" /\ m.src = q) }]
    /\ timeout' = [timeout EXCEPT 
        ![p] = [q \in Proc |-> 
            IF \E m \in inbox[p] : m.type = "alive" /\ m.src = q /\ q \in susp[p] 
                THEN timeout[p][q] + 1 
                ELSE timeout[p][q]]]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = 
        IF clock[p] + 1 >= ResetClock(p) THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED inbox

(* For model checking we abstract the delivery of messages *)
NoOp ==
    /\ UNCHANGED << clock, timeout, lastHeard, susp, outbox, inbox >>

Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)
    \/ NoOp

(* ------------------------------------------------------------------------- *)
(* Safety invariant (type correctness) *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ susp \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Message]
    /\ inbox \in [Proc -> SUBSET Message]
    /\ \A p \in Proc : SetMinus(outbox[p] \cup inbox[p], Messages) = {}

(* ------------------------------------------------------------------------- *)
(* Specification *)
(* ------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<clock, timeout, lastHeard, susp, outbox, inbox>>

=============================================================================