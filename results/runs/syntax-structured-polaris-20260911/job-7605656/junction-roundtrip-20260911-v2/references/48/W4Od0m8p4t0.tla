---- MODULE W4Od0m8p4t0 ----
EXTENDS Integers, FiniteSets

Teams == {"t1", "t2", "t3"}
Wings == {"g1", "g2"}
Rooms == {"o1", "o2", "o3", "o4"}
NONE == "none"
CAP == 2

WingOf == [o1 |-> "g1", o2 |-> "g1", o3 |-> "g2", o4 |-> "g2"]

VARIABLES coarse, fine, occ, crashed

vars == <<coarse, fine, occ, crashed>>

Init ==
    ( (coarse  = [w \in Wings |-> NONE])
     /\  (fine    = [r \in Rooms |-> NONE])
     /\  (occ     = {})
     /\  (crashed = [t \in Teams |-> FALSE]))

GrabCoarse(t, w) ==
    ( (~ crashed[t])
     /\  (coarse[w] = NONE)
     /\  (coarse' = [coarse EXCEPT ![w] = t])
     /\  (UNCHANGED <<fine, occ, crashed>>))

GrabFine(t, r) ==
    ( (~ crashed[t])
     /\  (coarse[WingOf[r]] = t)
     /\  (fine[r] = NONE)
     /\  (fine' = [fine EXCEPT ![r] = t])
     /\  (UNCHANGED <<coarse, occ, crashed>>))

Occupy(t, r) ==
    ( (~ crashed[t])
     /\  (fine[r] = t)
     /\  (coarse[WingOf[r]] = t)
     /\  (r \notin occ)
     /\  (Cardinality(occ) < CAP)
     /\  (occ' = occ \cup {r})
     /\  (UNCHANGED <<coarse, fine, crashed>>))

Vacate(r) ==
    ( (r \in occ)
     /\  (occ'    = occ \ {r})
     /\  (fine'   = [fine EXCEPT ![r] = NONE])
     /\  (coarse' = [coarse EXCEPT ![WingOf[r]] = NONE])
     /\  (UNCHANGED crashed))

Release(t, r) ==
    ( (fine[r] = t)
     /\  (r \notin occ)
     /\  (fine'   = [fine EXCEPT ![r] = NONE])
     /\  (coarse' = [coarse EXCEPT ![WingOf[r]] = NONE])
     /\  (UNCHANGED <<occ, crashed>>))

Crash(t) ==
    ( (~ crashed[t])
     /\  (crashed' = [crashed EXCEPT ![t] = TRUE])
     /\  (UNCHANGED <<coarse, fine, occ>>))

Recover(t) ==
    ( (crashed[t])
     /\  (crashed' = [crashed EXCEPT ![t] = FALSE])
     /\  (UNCHANGED <<coarse, fine, occ>>))

Next ==
    ( (\E t \in Teams, w \in Wings : GrabCoarse(t, w))
     \/  (\E t \in Teams, r \in Rooms : GrabFine(t, r))
     \/  (\E t \in Teams, r \in Rooms : Occupy(t, r))
     \/  (\E r \in Rooms : Vacate(r))
     \/  (\E t \in Teams, r \in Rooms : Release(t, r))
     \/  (\E t \in Teams : Crash(t))
     \/  (\E t \in Teams : Recover(t)))

Spec == Init /\ [][Next]_vars

TypeOK ==
    ( (coarse  \in [Wings -> Teams \cup {NONE}])
     /\  (fine    \in [Rooms -> Teams \cup {NONE}])
     /\  (occ     \subseteq Rooms)
     /\  (crashed \in [Teams -> BOOLEAN]))

WithinCapacity ==
    Cardinality(occ) <= CAP

====