---- MODULE W4Od17m3p0t5 ----
EXTENDS Naturals
CONSTANTS Nodes, MaxTerm
NONE == "none"
VARIABLES term, leader, operating, byAdmin
vars == <<term, leader, operating, byAdmin>>

Init ==
    ( (term = 0)
     /\  (leader = NONE)
     /\  (operating = [n \in Nodes |-> FALSE])
     /\  (byAdmin = [n \in Nodes |-> FALSE]))

Elect(n) ==
    ( (term < MaxTerm)
     /\  (term' = term + 1)
     /\  (leader' = n)
     /\  (UNCHANGED <<operating, byAdmin>>))

Operate(n) ==
    ( (leader = n)
     /\  (~operating[n])
     /\  (\A m \in Nodes : ~operating[m])
     /\  (operating' = [operating EXCEPT ![n] = TRUE])
     /\  (byAdmin' = [byAdmin EXCEPT ![n] = FALSE])
     /\  (UNCHANGED <<term, leader>>))

Stop(n) ==
    ( (operating[n])
     /\  (operating' = [operating EXCEPT ![n] = FALSE])
     /\  (byAdmin' = [byAdmin EXCEPT ![n] = FALSE])
     /\  (UNCHANGED <<term, leader>>))

FailLeader(n) ==
    ( (leader = n)
     /\  (leader' = NONE)
     /\  (operating' = [operating EXCEPT ![n] = IF byAdmin[n] THEN operating[n] ELSE FALSE])
     /\  (UNCHANGED <<term, byAdmin>>))

AdminSeize(n) ==
    ( (operating' = [m \in Nodes |-> m = n])
     /\  (byAdmin' = [m \in Nodes |-> m = n])
     /\  (UNCHANGED <<term, leader>>))

Next ==
    ( (\E n \in Nodes : Elect(n))
     \/  (\E n \in Nodes : Operate(n))
     \/  (\E n \in Nodes : Stop(n))
     \/  (\E n \in Nodes : FailLeader(n))
     \/  (\E n \in Nodes : AdminSeize(n))
     \/  (UNCHANGED vars))

Spec == Init /\ [][Next]_vars

DiverterMutex ==
    \A n1 \in Nodes, n2 \in Nodes :
        (operating[n1] /\ operating[n2]) => n1 = n2
====