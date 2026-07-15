---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants (to be supplied by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Proc,          \* Set of all processes
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,  \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages       \* Set of message identifiers (alive messages)

(*-----------------------------------------------------------------
  Type definitions
-----------------------------------------------------------------*)
ALIVE == "alive"

(* A message is a tuple <sender, type> *)
Message == [sender : Proc, type : {ALIVE}]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    suspicion,   \* [p \in Proc |-> Subset of Proc] – processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] – adaptive timeout for each pair
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] – ticks since p last heard from q
    clock,       \* [p \in Proc |-> Nat] – local clock of each process
    outbox       \* [p \in Proc |-> SUBSET Message] – messages p intends to send this step

vars == << suspicion, timeout, lastHeard, clock, outbox >>

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AllZeroLastHeard == \A p \in Proc: \A q \in Proc: lastHeard[p][q] = 0
AllDefaultTimeout == \A p \in Proc: \A q \in Proc: timeout[p][q] = d0
NoSuspicion == \A p \in Proc: suspicion[p] = {}

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Per‑process actions
-----------------------------------------------------------------*)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { [sender |-> p, type |-> ALIVE] } ]
    /\ \A q \in Proc: outbox'[p] = { [sender |-> p, type |-> ALIVE] }
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' =
        [lastHeard EXCEPT ![p][q] = IF q \in suspicion[p]
                                   THEN lastHeard[p][q] + 1
                                   ELSE lastHeard[p][q] + 1]  \* increment for all; no reset here
    /\ UNCHANGED << suspicion, timeout >>  \* No change to suspicion or timeout

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ let newSus == { q \in Proc :
                        q # p /\ lastHeard[p][q] > timeout[p][q] } \* may also include self? exclude self
       in
          /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1 \* for all q]
    /\ outbox' = outbox
    /\ UNCHANGED timeout

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \A m \in outbox[p] :
          /\ m.type = ALIVE
          /\ ~ (m.sender = p)          \* ignore own message
    /\ LET
          msgs == { m \in outbox[m.sender] :
                     m.type = ALIVE /\ m.sender # p }
       IN
          /\ lastHeard' = [lastHeard EXCEPT
                             ![p][q] = IF \E m \in msgs : m.sender = q
                                         THEN 0
                                         ELSE lastHeard[p][q] + 1 ]
          /\ suspicion' = [suspicion EXCEPT
                             ![p] = suspicion[p] \ { q \in suspicion[p] : \E m \in msgs : m.sender = q } ]
          /\ timeout' = [timeout EXCEPT
                           ![p][q] = IF \E m \in msgs : m.sender = q /\ q \in suspicion[p]
                                      THEN timeout[p][q] + 1
                                      ELSE timeout[p][q] ]
    /\ clock' = [clock EXCEPT ![p] =
                     IF clock[p] + 1 > SendPoint
                        /\ clock[p] + 1 > PredictPoint
                        /\ \A q \in Proc : clock[p] + 1 > timeout[p][q]
                     THEN 0
                     ELSE clock[p] + 1]
    /\ outbox' = outbox

ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Next ==
    \E p \in Proc: ProcStep(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ \A p \in Proc: suspicion[p] \subseteq Proc
    /\ \A p \in Proc: \A q \in Proc: timeout[p][q] \in Nat
    /\ \A p \in Proc: \A q \in Proc: lastHeard[p][q] \in Nat
    /\ \A p \in Proc: clock[p] \in Nat
    /\ \A p \in Proc: outbox[p] \subseteq Messages

=============================================================================