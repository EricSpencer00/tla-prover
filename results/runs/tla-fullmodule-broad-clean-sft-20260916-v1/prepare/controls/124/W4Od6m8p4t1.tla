---- MODULE W4Od6m8p4t1 ----
EXTENDS Naturals, FiniteSets

(* An elevator bank in a skyscraper admits passengers into two cars under a    *)
(* hierarchical locking discipline: an agent first takes the coarse bank lock, *)
(* then a fine per-car lock, and only then boards a waiting request into that   *)
(* car.  Boarding requests may be serviced in any order (messages reordered).  *)
(* The whole bank has a fixed occupancy ceiling that boarding must respect.     *)

CONSTANTS BankCap, MaxReq

Agents == {"a1", "a2"}
Cars   == {"c1", "c2"}
Free   == "free"

VARIABLES coarse, fine, load, pending, served

vars == << coarse, fine, load, pending, served >>

TotalLoad == load["c1"] + load["c2"]

TypeOK ==
    /\ coarse \in Agents \cup {Free}
    /\ fine \in [Cars -> Agents \cup {Free}]
    /\ load \in [Cars -> Nat]
    /\ pending \subseteq (1..MaxReq)
    /\ served \subseteq (1..MaxReq)

Init ==
    /\ coarse = Free
    /\ fine = [c \in Cars |-> Free]
    /\ load = [c \in Cars |-> 0]
    /\ pending = 1..MaxReq
    /\ served = {}

AcquireCoarse(a) ==
    /\ coarse = Free
    /\ coarse' = a
    /\ UNCHANGED << fine, load, pending, served >>

AcquireFine(a, c) ==
    /\ coarse = a
    /\ fine[c] = Free
    /\ fine' = [fine EXCEPT ![c] = a]
    /\ UNCHANGED << coarse, load, pending, served >>

\* Board any waiting request into a car, respecting the bank ceiling.
Board(a, c, req) ==
    /\ coarse = a
    /\ fine[c] = a
    /\ req \in pending
    /\ TotalLoad < BankCap
    /\ load' = [load EXCEPT ![c] = load[c] + 1]
    /\ pending' = pending \ {req}
    /\ served' = served \cup {req}
    /\ UNCHANGED << coarse, fine >>

ReleaseFine(a, c) ==
    /\ fine[c] = a
    /\ fine' = [fine EXCEPT ![c] = Free]
    /\ UNCHANGED << coarse, load, pending, served >>

ReleaseCoarse(a) ==
    /\ coarse = a
    /\ coarse' = Free
    /\ UNCHANGED << fine, load, pending, served >>

Next ==
    \/ \E a \in Agents : AcquireCoarse(a)
    \/ \E a \in Agents, c \in Cars : AcquireFine(a, c)
    \/ \E a \in Agents, c \in Cars, req \in 1..MaxReq : Board(a, c, req)
    \/ \E a \in Agents, c \in Cars : ReleaseFine(a, c)
    \/ \E a \in Agents : ReleaseCoarse(a)

Spec == Init /\ [][Next]_vars

(* The bank never carries more passengers than its fixed occupancy ceiling.    *)
WithinCapacity == TotalLoad <= BankCap
====