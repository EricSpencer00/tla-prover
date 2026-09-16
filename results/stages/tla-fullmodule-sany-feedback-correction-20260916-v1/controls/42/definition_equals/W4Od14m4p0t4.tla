---- MODULE W4Od14m4p0t4 ----
EXTENDS Integers
VARIABLES holders, queue, cap
Init = holders = 0 /\ queue = 0 /\ cap = 2
Grab == holders = 0 /\ holders' = (holders) + 1 /\ UNCHANGED <<queue, cap>>
Release == holders > 0 /\ holders' = holders - 1 /\ UNCHANGED <<queue, cap>>
Enqueue == queue < cap /\ queue' = queue + 1 /\ UNCHANGED <<holders, cap>>
Drain == queue > 0 /\ queue' = queue - 1 /\ UNCHANGED <<holders, cap>>
Reconfig == \E c \in {2, 3} : c >= queue /\ cap' = c /\ UNCHANGED <<holders, queue>>
Next == Grab \/ Release \/ Enqueue \/ Drain \/ Reconfig
Spec == Init /\ [][Next]_<<holders, queue, cap>>
ExclusiveDownlink == holders >= 0 /\ holders <= 1 /\ queue >= 0 /\ queue <= cap
====