---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

(* ---------------------------------------------------------------------- *)
(*  Types and helper definitions                                           *)
(* ---------------------------------------------------------------------- *)

(* A message is a record with source, destination and a type label. *)
Message == [src : Proc, dst : Proc, typ : {"alive"}]

AliveMessage(p, q) == [src |-> p, dst |-> q, typ |-> "alive"]

(* ---------------------------------------------------------------------- *)
(*  Variables                                                             *)
(* ---------------------------------------------------------------------- *)

VARIABLES clk, suspicion, timeout, lastHeard, outMsgs

vars == <<clk, suspicion, timeout, lastHeard, outMsgs>>

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                          *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ clk = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outMsgs = [p \in Proc |-> {}]

(* ---------------------------------------------------------------------- *)
(*  Action definitions                                                     *)
(* ---------------------------------------------------------------------- *)

SendCond(p) == 
    /\ (clk[p] % SendPoint) = 0
    /\ (clk[p] % PredictPoint) # 0

PredictCond(p) ==
    /\ (clk[p] % PredictPoint) = 0
    /\ (clk[p] % SendPoint) # 0

(* Send alive messages to all other processes *)
SendAlive(p) ==
    /\ SendCond(p)
    /\ outMsgs' = [outMsgs EXCEPT ![p] = outMsgs[p] \cup 
                      {AliveMessage(p, q) : q \in Proc \ {p}}]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ suspicion' = suspicion
    /\ timeout' = timeout
    /\ lastHeard' = [lastHeard EXCEPT 
                       ![p][q] = 
                         IF q # p /\ lastHeard[p][q] < timeout[p][q] 
                         THEN lastHeard[p][q] + 1 
                         ELSE lastHeard[p][q] 
                     \* other processes unchanged
                     ]
    /\ UNCHANGED <<clk, suspicion, timeout, lastHeard, outMsgs>> \* will be overridden by primed definitions

(* Make predictions based on timeout expirations *)
MakePrediction(p) ==
    /\ PredictCond(p)
    /\ suspicion' = [suspicion EXCEPT 
                       ![p] = suspicion[p] \cup
                               { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } ]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
                       ![p][q] = IF q # p THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] ]
    /\ outMsgs' = outMsgs
    /\ timeout' = timeout

(* Receive incoming alive messages (abstracted) *)
Receive(p) ==
    /\ ~SendCond(p)
    /\ ~PredictCond(p)
    /\ \E R \subseteq Proc \ {p} :
         /\ \A q \in R : AliveMessage(q, p) \in outMsgs[q]   \* message was sent
         /\ outMsgs' = outMsgs
         /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
         /\ suspicion' = [suspicion EXCEPT 
                             ![p] = suspicion[p] \ { q \in R } ]
         /\ lastHeard' = [lastHeard EXCEPT 
                             ![p][q] = IF q \in R THEN 0 ELSE lastHeard[p][q] ]
         /\ timeout' = [timeout EXCEPT 
                           ![p][q] = IF q \in R /\ q \in suspicion[p] 
                                      THEN timeout[p][q] + 1 
                                      ELSE timeout[p][q] ]
    /\ UNCHANGED <<clk, suspicion, timeout, lastHeard, outMsgs>> \* overridden by primed definitions

(* ---------------------------------------------------------------------- *)
(*  Next-state relation                                                    *)
(* ---------------------------------------------------------------------- *)

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : MakePrediction(p)
    \/ \E p \in Proc : Receive(p)

(* ---------------------------------------------------------------------- *)
(*  Type invariant                                                         *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
    /\ clk \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outMsgs \in [Proc -> SUBSET Messages]

(* ---------------------------------------------------------------------- *)
(*  Specification                                                          *)
(* ---------------------------------------------------------------------- *)

SPECIFICATION == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(*  Assumptions about constants                                            *)
(* ---------------------------------------------------------------------- *)

ASSUME SendPoint > 0
ASSUME PredictPoint > 0
ASSUME SendPoint # PredictPoint
ASSUME ~(\E k \in Nat : SendPoint = k * PredictPoint)
ASSUME ~(\E k \in Nat : PredictPoint = k * SendPoint)

(* ---------------------------------------------------------------------- *)
(*  Exported identifiers                                                   *)
(* ---------------------------------------------------------------------- *)

THEOREM InitIsInit == Init
INVARIANT TypeOK

====