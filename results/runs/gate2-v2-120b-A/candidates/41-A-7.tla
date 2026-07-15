---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Constants (these will be instantiated in the .cfg file)               *)
(***************************************************************************)
CONSTANT Proc
CONSTANT d0
CONSTANT SendPoint
CONSTANT PredictPoint
CONSTANT Messages

(***************************************************************************)
(*  Derived sets                                                          *)
(***************************************************************************)
ProcPair == { <<p, q>> : p \in Proc, q \in Proc, p # q }

(***************************************************************************)
(*  State variables                                                      *)
(***************************************************************************)
VARIABLES
    clock,          \* [Proc -> Nat]
    susSet,         \* [Proc -> SUBSET Proc]
    timeout,        \* [Proc -> [Proc -> Nat]]
    lastHeard,      \* [Proc -> [Proc -> Nat]]
    outMsgSet       \* Set of messages in transit (each message = <<src, dst>>)

vars == <<clock, susSet, timeout, lastHeard, outMsgSet>>

(***************************************************************************)
(*  Helper definitions                                                   *)
(***************************************************************************)
Alive(p, q) == <<p, q>>                     \* the alive message from p to q

MsgFrom(p)(msg) == msg[1] = p               \* message originates from p

MsgTo(q)(msg) == msg[2] = q                 \* message destined to q

(***************************************************************************)
(*  Initialization                                                       *)
(***************************************************************************)
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ susSet = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE 0]]
    /\ outMsgSet = {}

(***************************************************************************)
(*  Actions                                                              *)
(***************************************************************************)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ \A q \in Proc : q # p => outMsgSet' = outMsgSet \cup {Alive(p, q)}
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1
                                         FOR q \in Proc : q # p]
    /\ UNCHANGED <<susSet, timeout, outMsgSet>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ susSet' = [susSet EXCEPT ![p] = @ \cup
         { q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1
                                         FOR q \in Proc : q # p]
    /\ UNCHANGED <<timeout, outMsgSet>>

Receive(p) ==
    /\ \A q \in Proc : q # p => ~ (clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint = 0)
    /\ \E M \subseteq outMsgSet :
        ( \A msg \in M : MsgTo(p)(msg) )
        /\ outMsgSet' = (outMsgSet \ M)
        /\ \A msg \in M :
            LET src == msg[1] IN
                /\ lastHeard' = [lastHeard EXCEPT ![p][src] = 0]
                /\ susSet' = [susSet EXCEPT ![p] = @ \ {src}]
                /\ timeout' = IF src \in susSet[p]
                               THEN [timeout EXCEPT ![p][src] = @ + 1]
                               ELSE timeout
        /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint
                                      THEN 0 ELSE @ + 1]
    /\ UNCHANGED outMsgSet

(***************************************************************************)
(*  Next-state relation                                                   *)
(***************************************************************************)
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(***************************************************************************)
(*  Specification (temporal)                                              *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Type invariant (the only invariant required by the cfg)               *)
(***************************************************************************)
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ susSet \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outMsgSet \subseteq Messages

(***************************************************************************)
(*  Exported definitions                                                  *)
(***************************************************************************)
INIT == Init
NEXT == Next
INVARIANTS == TypeOK

=============================================================================