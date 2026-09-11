---- MODULE W4Od12m4p3t4 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Units, Bins, QCap, Empty

VARIABLES waiting, queue, binHolder, openBins, liveBins

vars == <<waiting, queue, binHolder, openBins, liveBins>>

Init ==
    ( (waiting = Units)
     /\  (queue = {})
     /\  (binHolder = [bn \in Bins |-> Empty])
     /\  (openBins = Bins)
     /\  (liveBins = Bins))

Submit(u) ==
    ( (u \in waiting)
     /\  (Cardinality(queue) < QCap)
     /\  (waiting' = waiting \ {u})
     /\  (queue' = queue \cup {u})
     /\  (UNCHANGED <<binHolder, openBins, liveBins>>))

Cancel(u) ==
    ( (u \in queue)
     /\  (queue' = queue \ {u})
     /\  (waiting' = waiting \cup {u})
     /\  (UNCHANGED <<binHolder, openBins, liveBins>>))

Allocate(u, bn) ==
    ( (u \in queue)
     /\  (bn \in liveBins)
     /\  (bn \in openBins)
     /\  (binHolder' = [binHolder EXCEPT ![bn] = u])
     /\  (openBins' = openBins \ {bn})
     /\  (queue' = queue \ {u})
     /\  (UNCHANGED <<waiting, liveBins>>))

Free(bn) ==
    ( (binHolder[bn] # Empty)
     /\  (waiting' = waiting \cup {binHolder[bn]})
     /\  (binHolder' = [binHolder EXCEPT ![bn] = Empty])
     /\  (openBins' = IF bn \in liveBins THEN openBins \cup {bn} ELSE openBins)
     /\  (UNCHANGED <<queue, liveBins>>))

AddBin(bn) ==
    ( (bn \notin liveBins)
     /\  (liveBins' = liveBins \cup {bn})
     /\  (openBins' = IF binHolder[bn] = Empty THEN openBins \cup {bn} ELSE openBins)
     /\  (UNCHANGED <<waiting, queue, binHolder>>))

RemoveBin(bn) ==
    ( (bn \in liveBins)
     /\  (binHolder[bn] = Empty)
     /\  (liveBins' = liveBins \ {bn})
     /\  (openBins' = openBins \ {bn})
     /\  (UNCHANGED <<waiting, queue, binHolder>>))

Next ==
    ( (\E u \in Units : Submit(u) \/ Cancel(u))
     \/  (\E u \in Units, bn \in Bins : Allocate(u, bn))
     \/  (\E bn \in Bins : Free(bn) \/ AddBin(bn) \/ RemoveBin(bn)))

Spec == Init /\ [][Next]_vars

OccupiedBinNotOpen ==
    \A bn \in Bins : (binHolder[bn] # Empty) => (bn \notin openBins)
====