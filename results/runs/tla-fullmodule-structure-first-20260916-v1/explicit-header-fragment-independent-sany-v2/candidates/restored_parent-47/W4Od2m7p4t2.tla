---- MODULE W4Od2m7p4t2 ----
VARIABLES Dispatchers, Cap, Active, ReadSnapshots

CONSTANTS Dispatchers, Cap

Init == Active = 0 /\ ReadSnapshots = [d \in Dispatchers |-> 0]

Next == \E d \in Dispatchers : ReadSnapshots[d] < Cap /\ ReadSnapshots[d] = Active
                      /\ \A d' \in Dispatchers : ReadSnaphots[d'] = ReadSnapshots[d']
                      -> (Active' = Active + 1) /\ ReadSnapshots' = ReadSnapshots
                      \/ \E d \in Dispatchers, c \in 0..Cap : ReadSnapshots[d] = Active /\ ReadSnapshots[d] < Cap
                      /\ \A d'!= d \in Dispatchers : Readsnapshots[d'] = ReadSnapshots[d]
                      /\ \A d' \neq d \in Dispatchers : ReadSnaphots[d'] = ReadSnapshots[d']'
                      -> (Active' = Active) /\ ReadSnapshots' = [d' \in Dispatchers |-> IF d' = d THEN ReadSnapshots[d] + 1 ELSE ReadSnapshots[d']])

Spec == Init /\ [][Next]_<<Dispatchers, Cap, Active, ReadSnaphots>>

====