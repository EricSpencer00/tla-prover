-------------------------- MODULE W4Od4m3p4t1 --------------------------
EXTENDS Naturals

CONSTANTS Controllers, Tickets, NoOne, Cap, MaxTerm

VARIABLES
    term,       \* current election term
    leader,     \* current leader controller, or NoOne
    onLine,     \* number of cars currently on the conveyor
    status      \* status[t] : "free" | "enterQ" | "exitQ" | "done"

vars == << term, leader, onLine, status >>

TypeOK ==
    /\ term \in 0..MaxTerm
    /\ leader \in (Controllers \cup {NoOne})
    /\ onLine \in 0..Cap
    /\ status \in [Tickets -> {"free", "enterQ", "exitQ", "done"}]

Init ==
    /\ term = 0
    /\ leader = NoOne
    /\ onLine = 0
    /\ status = [t \in Tickets |-> "free"]

Elect(c) ==
    /\ leader = NoOne
    /\ leader' = c
    /\ term' = IF term < MaxTerm THEN term + 1 ELSE term
    /\ UNCHANGED << onLine, status >>

Fail(c) ==
    /\ leader = c
    /\ leader' = NoOne
    /\ UNCHANGED << term, onLine, status >>

\* Only the leader issues tickets into the shared queue.
IssueEnter(c, t) ==
    /\ leader = c
    /\ status[t] = "free"
    /\ status' = [status EXCEPT ![t] = "enterQ"]
    /\ UNCHANGED << term, leader, onLine >>

IssueExit(c, t) ==
    /\ leader = c
    /\ status[t] = "free"
    /\ status' = [status EXCEPT ![t] = "exitQ"]
    /\ UNCHANGED << term, leader, onLine >>

\* Any pending ticket may be applied in any order (messages are reordered).
ApplyEnter(t) ==
    /\ status[t] = "enterQ"
    /\ onLine < Cap
    /\ onLine' = onLine + 1
    /\ status' = [status EXCEPT ![t] = "done"]
    /\ UNCHANGED << term, leader >>

ApplyExit(t) ==
    /\ status[t] = "exitQ"
    /\ onLine > 0
    /\ onLine' = onLine - 1
    /\ status' = [status EXCEPT ![t] = "done"]
    /\ UNCHANGED << term, leader >>

Next ==
    \/ \E c \in Controllers : Elect(c)
    \/ \E c \in Controllers : Fail(c)
    \/ \E c \in Controllers, t \in Tickets : IssueEnter(c, t)
    \/ \E c \in Controllers, t \in Tickets : IssueExit(c, t)
    \/ \E t \in Tickets : ApplyEnter(t)
    \/ \E t \in Tickets : ApplyExit(t)

Spec == Init /\ [][Next]_vars

\* Bounded capacity: the conveyor is never over-filled.
WithinCapacity == onLine <= Cap

=============================================================================
