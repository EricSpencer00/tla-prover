---- MODULE W4Od14m7p2t1 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Drones, Depots, Allocation, NoDepot, NoRead

\* readOn/readVal are the drone's outstanding reading of a depot counter; the
\* write only lands if the counter still agrees with it.
VARIABLES remaining, issued, carrying, readOn, readVal

vars == << remaining, issued, carrying, readOn, readVal >>

TypeOK ==
    ( (remaining \in [Depots -> 0..Allocation])
     /\  (issued \in [Depots -> 0..Allocation])
     /\  (carrying \in [Drones -> Depots \cup {NoDepot}])
     /\  (readOn \in [Drones -> Depots \cup {NoDepot}])
     /\  (readVal \in [Drones -> (0..Allocation) \cup {NoRead}]))

Init ==
    ( (remaining = [dp \in Depots |-> Allocation])
     /\  (issued = [dp \in Depots |-> 0])
     /\  (carrying = [d \in Drones |-> NoDepot])
     /\  (readOn = [d \in Drones |-> NoDepot])
     /\  (readVal = [d \in Drones |-> NoRead]))

ReadLevel(d, dp) ==
    ( (carrying[d] = NoDepot)
     /\  (readOn[d] = NoDepot)
     /\  (readOn' = [readOn EXCEPT ![d] = dp])
     /\  (readVal' = [readVal EXCEPT ![d] = remaining[dp]])
     /\  (UNCHANGED << remaining, issued, carrying >>))

\* The unit leaves the depot and joins the issued total in the same step, so
\* the depot's books cannot come apart even when a read went stale.
TakeLoad(d) ==
    ( (readOn[d] # NoDepot)
     /\  (readVal[d] = remaining[readOn[d]])
     /\  (readVal[d] > 0)
     /\  (remaining' = [remaining EXCEPT ![readOn[d]] = readVal[d] - 1])
     /\  (issued' = [issued EXCEPT ![readOn[d]] = @ + 1])
     /\  (carrying' = [carrying EXCEPT ![d] = readOn[d]])
     /\  (readOn' = [readOn EXCEPT ![d] = NoDepot])
     /\  (readVal' = [readVal EXCEPT ![d] = NoRead]))

DiscardRead(d) ==
    ( (readOn[d] # NoDepot)
     /\  (readOn' = [readOn EXCEPT ![d] = NoDepot])
     /\  (readVal' = [readVal EXCEPT ![d] = NoRead])
     /\  (UNCHANGED << remaining, issued, carrying >>))

DropLoad(d) ==
    ( (carrying[d] # NoDepot)
     /\  (carrying' = [carrying EXCEPT ![d] = NoDepot])
     /\  (UNCHANGED << remaining, issued, readOn, readVal >>))

Next ==
    ( (\E d \in Drones, dp \in Depots : ReadLevel(d, dp))
     \/  (\E d \in Drones : TakeLoad(d) \/ DiscardRead(d) \/ DropLoad(d)))

\* Nothing can block a drop, so weak fairness per drone is enough.
Spec == Init /\ [][Next]_vars
    /\ \A d \in Drones :
        ( (TRUE)
         /\  (WF_vars(DropLoad(d))))

DepotBooksBalance ==
    \A dp \in Depots : remaining[dp] + issued[dp] = Allocation

EveryLoadIsDropped ==
    \A d \in Drones : (carrying[d] # NoDepot) ~> (carrying[d] = NoDepot)

====