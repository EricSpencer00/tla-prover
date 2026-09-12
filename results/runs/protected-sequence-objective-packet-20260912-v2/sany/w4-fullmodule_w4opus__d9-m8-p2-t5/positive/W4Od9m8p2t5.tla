---------------------------- MODULE W4Od9m8p2t5 ----------------------------
(* Hierarchical (coarse-then-fine) locking gates ordinary shed/restore of  *)
(* circuit load into a shared reserve pool. A privileged admin override    *)
(* can shed or restore any circuit directly, bypassing both lock levels,   *)
(* and is what actually guarantees every shed circuit gets restored.       *)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Region, Agent, NoAgent, c1, c2, Nom1, Nom2

ASSUME NoAgent \notin Agent
ASSUME Nom1 \in Nat /\ Nom2 \in Nat

Circuit == {c1, c2}
Nominal == (c1 :> Nom1 @@ c2 :> Nom2)

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + SumSet(f, S \ {x})

TotalNominal == SumSet(Nominal, Circuit)

VARIABLES regionLock, circuitLock, supply, reserve

vars == <<regionLock, circuitLock, supply, reserve>>

TypeOK ==
    /\ regionLock \in [Region -> Agent \cup {NoAgent}]
    /\ circuitLock \in [Circuit -> Agent \cup {NoAgent}]
    /\ supply \in [Circuit -> Nat]
    /\ \A c \in Circuit : supply[c] <= Nominal[c]
    /\ reserve \in 0..TotalNominal

Init ==
    /\ regionLock = [r \in Region |-> NoAgent]
    /\ circuitLock = [c \in Circuit |-> NoAgent]
    /\ supply = [c \in Circuit |-> Nominal[c]]
    /\ reserve = 0

AcquireRegion(g, r) ==
    /\ regionLock[r] = NoAgent
    /\ regionLock' = [regionLock EXCEPT ![r] = g]
    /\ UNCHANGED <<circuitLock, supply, reserve>>

ReleaseRegion(g, r) ==
    /\ regionLock[r] = g
    /\ regionLock' = [regionLock EXCEPT ![r] = NoAgent]
    /\ UNCHANGED <<circuitLock, supply, reserve>>

AcquireCircuit(g, r, c) ==
    /\ regionLock[r] = g
    /\ circuitLock[c] = NoAgent
    /\ circuitLock' = [circuitLock EXCEPT ![c] = g]
    /\ UNCHANGED <<regionLock, supply, reserve>>

ReleaseCircuit(g, c) ==
    /\ circuitLock[c] = g
    /\ circuitLock' = [circuitLock EXCEPT ![c] = NoAgent]
    /\ UNCHANGED <<regionLock, supply, reserve>>

ShedLoad(g, c) ==
    /\ circuitLock[c] = g
    /\ supply[c] = Nominal[c]
    /\ supply' = [supply EXCEPT ![c] = 0]
    /\ reserve' = reserve + Nominal[c]
    /\ UNCHANGED <<regionLock, circuitLock>>

RestoreLoad(g, c) ==
    /\ circuitLock[c] = g
    /\ supply[c] = 0
    /\ reserve >= Nominal[c]
    /\ supply' = [supply EXCEPT ![c] = Nominal[c]]
    /\ reserve' = reserve - Nominal[c]
    /\ UNCHANGED <<regionLock, circuitLock>>

AdminShed(c) ==
    /\ supply[c] = Nominal[c]
    /\ supply' = [supply EXCEPT ![c] = 0]
    /\ reserve' = reserve + Nominal[c]
    /\ UNCHANGED <<regionLock, circuitLock>>

AdminRestore(c) ==
    /\ supply[c] = 0
    /\ reserve >= Nominal[c]
    /\ supply' = [supply EXCEPT ![c] = Nominal[c]]
    /\ reserve' = reserve - Nominal[c]
    /\ UNCHANGED <<regionLock, circuitLock>>

Next_ ==
    \/ \E g \in Agent, r \in Region : AcquireRegion(g, r) \/ ReleaseRegion(g, r)
    \/ \E g \in Agent, r \in Region, c \in Circuit : AcquireCircuit(g, r, c)
    \/ \E g \in Agent, c \in Circuit : ReleaseCircuit(g, c) \/ ShedLoad(g, c) \/ RestoreLoad(g, c)
    \/ \E c \in Circuit : AdminShed(c) \/ AdminRestore(c)

(* The admin override is the guaranteed backstop: whichever circuit is    *)
(* shed, its restore is forced regardless of ordinary lock contention.   *)
AdminFair(c) == WF_vars(AdminRestore(c))

Spec == Init /\ [][Next_]_vars /\ (\A c \in Circuit : AdminFair(c))

(* Load only moves between circuits and the reserve; the grand total is   *)
(* always the feeder's fixed nominal demand -- nothing created/destroyed. *)
Conservation == SumSet(supply, Circuit) + reserve = TotalNominal

(* Every shed circuit is eventually restored to full supply. *)
EventualRestore == \A c \in Circuit : (supply[c] = 0) ~> (supply[c] = Nominal[c])
=============================================================================