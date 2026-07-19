-------------------------- MODULE W4Od16m3p0t5 --------------------------
EXTENDS Naturals

CONSTANTS Nodes, NoOne, MaxTerm

VARIABLES
    term,       \* current election term
    leader,     \* current leader node, or NoOne
    pc,         \* pc[n] : "idle" | "waiting" | "dispensing"
    adminBusy   \* TRUE iff the administrator holds the cabinet

vars == << term, leader, pc, adminBusy >>

TypeOK ==
    /\ term \in 0..MaxTerm
    /\ leader \in (Nodes \cup {NoOne})
    /\ pc \in [Nodes -> {"idle", "waiting", "dispensing"}]
    /\ adminBusy \in BOOLEAN

Init ==
    /\ term = 0
    /\ leader = NoOne
    /\ pc = [n \in Nodes |-> "idle"]
    /\ adminBusy = FALSE

Elect(n) ==
    /\ leader = NoOne
    /\ leader' = n
    /\ term' = IF term < MaxTerm THEN term + 1 ELSE term
    /\ UNCHANGED << pc, adminBusy >>

Fail(n) ==
    /\ leader = n
    /\ leader' = NoOne
    /\ UNCHANGED << term, pc, adminBusy >>

Request(n) ==
    /\ pc[n] = "idle"
    /\ pc' = [pc EXCEPT ![n] = "waiting"]
    /\ UNCHANGED << term, leader, adminBusy >>

\* The leader enters only when no node is dispensing and admin is out.
Enter(n) ==
    /\ leader = n
    /\ pc[n] = "waiting"
    /\ ~adminBusy
    /\ \A m \in Nodes : pc[m] # "dispensing"
    /\ pc' = [pc EXCEPT ![n] = "dispensing"]
    /\ UNCHANGED << term, leader, adminBusy >>

Exit(n) ==
    /\ pc[n] = "dispensing"
    /\ pc' = [pc EXCEPT ![n] = "idle"]
    /\ UNCHANGED << term, leader, adminBusy >>

\* Admin override: force any dispenser out, revoke leadership, take control.
AdminEnter ==
    /\ ~adminBusy
    /\ adminBusy' = TRUE
    /\ pc' = [n \in Nodes |-> IF pc[n] = "dispensing" THEN "idle" ELSE pc[n]]
    /\ leader' = NoOne
    /\ UNCHANGED term

AdminExit ==
    /\ adminBusy
    /\ adminBusy' = FALSE
    /\ UNCHANGED << term, leader, pc >>

Next ==
    \/ \E n \in Nodes : Elect(n)
    \/ \E n \in Nodes : Fail(n)
    \/ \E n \in Nodes : Request(n)
    \/ \E n \in Nodes : Enter(n)
    \/ \E n \in Nodes : Exit(n)
    \/ AdminEnter
    \/ AdminExit

Spec == Init /\ [][Next]_vars

\* Mutual exclusion on the cabinet: at most one operator, node or admin.
MutualExclusion ==
    /\ \A m, n \in Nodes :
          (pc[m] = "dispensing" /\ pc[n] = "dispensing") => (m = n)
    /\ (adminBusy => \A n \in Nodes : pc[n] # "dispensing")

=============================================================================
