---- MODULE W4Od1m9p0t3 ----
EXTENDS Naturals
CONSTANTS Flights, MaxEpoch
VARIABLES occupant, epoch, grants, completed
vars == <<occupant, epoch, grants, completed>>

Init ==
    ( (occupant = {})
     /\  (epoch = 0)
     /\  (grants = {})
     /\  (completed = {}))

IssueGrant(fl) ==
    ( (fl \notin completed)
     /\  (<<fl, epoch>> \notin grants)
     /\  (grants' = grants \cup {<<fl, epoch>>})
     /\  (UNCHANGED <<occupant, epoch, completed>>))

Enter(fl) ==
    ( (occupant = {})
     /\  (<<fl, epoch>> \in grants)
     /\  (fl \notin completed)
     /\  (occupant' = {fl})
     /\  (UNCHANGED <<epoch, grants, completed>>))

Leave(fl) ==
    ( (fl \in occupant)
     /\  (occupant' = occupant \ {fl})
     /\  (completed' = completed \cup {fl})
     /\  (UNCHANGED <<epoch, grants>>))

Reconfigure ==
    ( (epoch < MaxEpoch)
     /\  (epoch' = epoch + 1)
     /\  (UNCHANGED <<occupant, grants, completed>>))

Next ==
    ( (\E fl \in Flights : IssueGrant(fl) \/ Enter(fl) \/ Leave(fl))
     \/  (Reconfigure)
     \/  (UNCHANGED vars))

Spec == Init /\ [][Next]_vars

RunwayMutex == \A f1, f2 \in occupant : f1 = f2
====