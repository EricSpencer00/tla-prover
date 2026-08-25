---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(*  Constants (to be supplied by the .cfg file)                            *)
(***************************************************************************)
CONSTANTS 
    Proc,           \* Set of process identifiers
    d0,             \* Default timeout value (positive integer)
    SendPoint,      \* Send interval (positive integer)
    PredictPoint,   \* Predict interval (positive integer)
    Messages        \* Set of all possible messages

(***************************************************************************)
(*  Derived definitions                                                    *)
(***************************************************************************)

(* The kind of alive messages *)
AliveKind == "Alive"

(* Helper function to build an alive message *)
AliveMsg(p, q) == [src |-> p, dst |-> q, kind |-> AliveKind]

(* The set of all alive messages that a process p can create *)
AliveMsgs(p) == { AliveMsg(p, q) : q \in Proc \ {p} }

(* Maximum of a set of naturals; defaults to 0 for empty set *)
MaxNat(S) == IF S = {} THEN 0 ELSE
               CHOOSE n \in Nat : n \in S /\ \A m \in S : m <= n

(***************************************************************************)
(*  Variables                                                             *)
(***************************************************************************)

VARIABLES 
    suspicion,   \* [Proc -> SUBSET Proc]   : current suspicion sets
    timeout,     \* [Proc -> [Proc -> Nat]] : adaptive timeout intervals
    lastHeard,   \* [Proc -> [Proc -> Nat]] : counters since last alive
    clk,         \* [Proc -> Nat]           : local clocks
    outMsgs      \* SUBSET Messages          : messages to be sent in this step

vars == << suspicion, timeout, lastHeard, clk, outMsgs >>

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk       = [p \in Proc |-> 0]
    /\ outMsgs   = {}

(***************************************************************************)
(*  Type invariant                                                         *)
(***************************************************************************)

TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clk       \in [Proc -> Nat]
    /\ outMsgs   \subseteq Messages

(***************************************************************************)
(*  Helper definitions for clock handling                                 *)
(***************************************************************************)

(* The maximal relevant threshold for process p *)
MaxThreshold(p) ==
    MaxNat({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })

NextClock(p, c) ==
    IF c + 1 > MaxThreshold(p) THEN 0 ELSE c + 1

(***************************************************************************)
(*  Process actions                                                       *)
(***************************************************************************)

(* 1. Send alive messages *)
Send(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0            \* send and predict never coincide
    /\ outMsgs' = outMsgs \cup AliveMsgs(p)
    /\ suspicion' = suspicion
    /\ timeout'   = timeout
    /\ clk'       = [clk EXCEPT ![p] = NextClock(p, clk[p])]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p] = [q \in Proc |-> 
                                 IF q \in Proc \ {p} /\ lastHeard[p][q] < timeout[p][q]
                                 THEN lastHeard[p][q] + 1
                                 ELSE lastHeard[p][q]]]

(* 2. Predict (update suspicion set) *)
Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT
                        ![p] = suspicion[p] \cup
                               { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ timeout'   = timeout
    /\ outMsgs'   = outMsgs
    /\ clk'       = [clk EXCEPT ![p] = NextClock(p, clk[p])]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p] = [q \in Proc |-> 
                                 IF q \in Proc \ {p} /\ lastHeard[p][q] < timeout[p][q]
                                 THEN lastHeard[p][q] + 1
                                 ELSE lastHeard[p][q]]]

(* 3. Receive messages (any subset of incoming alive messages) *)
Receive(p) ==
    \E recv \in SUBSET { m \in Messages : m.dst = p } :
        /\ outMsgs'   = outMsgs
        /\ suspicion' = [suspicion EXCEPT
                            ![p] = suspicion[p] \ { src : src \in { m.src : m \in recv } }]
        /\ timeout'   = [timeout EXCEPT
                            ![p][src] = 
                                IF src \in { m.src : m \in recv } /\ src \in suspicion[p]
                                THEN timeout[p][src] + 1
                                ELSE timeout[p][src] 
                         | src \in Proc]
        /\ clk'       = [clk EXCEPT ![p] = NextClock(p, clk[p])]
        /\ lastHeard' = [lastHeard EXCEPT
                            ![p] = [q \in Proc |-> 
                                      IF q \in { m.src : m \in recv }
                                      THEN 0
                                      ELSE IF q \in Proc \ {p} /\ lastHeard[p][q] < timeout[p][q]
                                           THEN lastHeard[p][q] + 1
                                           ELSE lastHeard[p][q]]]

(* 4. Stuttering (no process takes a step) – needed for completeness *)
Stutter ==
    UNCHANGED vars

(***************************************************************************)
(*  Next-state relation                                                    *)
(***************************************************************************)

Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)
    \/ Stutter

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)

SPECIFICATION ==
    Init /\ [][Next]_vars

(***************************************************************************)
(*  Exported identifiers                                                   *)
(***************************************************************************)

Init == Init
Next == Next
TypeOK == TypeOK
SPECIFICATION == SPECIFICATION
PROPERTIES == SPECIFICATION

=============================================================================