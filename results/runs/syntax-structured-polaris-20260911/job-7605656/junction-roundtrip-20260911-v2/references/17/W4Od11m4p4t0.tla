---- MODULE W4Od11m4p4t0 ----
EXTENDS Naturals, Sequences
CONSTANTS Docs, Printers, MaxCap
VARIABLES queue, capacity, active, crashed

TypeInv ==
    ( (queue \in Seq(Docs))
     /\  (capacity \in 1..MaxCap)
     /\  (active \in 0..Printers)
     /\  (crashed \in BOOLEAN))

\* A document is spooled into the bounded queue only while it has room; a full
\* queue exerts backpressure and refuses the submission.
Enqueue ==
    ( (Len(queue) < capacity)
     /\  (\E d \in Docs : queue' = Append(queue, d))
     /\  (UNCHANGED <<capacity, active, crashed>>))

\* A printer (if the spooler is up) pulls the head job and begins printing it,
\* but only while a printer is free.
StartPrint ==
    ( (~crashed)
     /\  (Len(queue) > 0)
     /\  (active < Printers)
     /\  (queue' = Tail(queue))
     /\  (active' = active + 1)
     /\  (UNCHANGED <<capacity, crashed>>))

\* A printer finishes a job and becomes free again.
FinishPrint ==
    ( (active > 0)
     /\  (active' = active - 1)
     /\  (UNCHANGED <<queue, capacity, crashed>>))

\* Capacity is reconfigured at runtime but never below the current queue length.
Reconfigure ==
    ( (\E c \in 1..MaxCap :
         ( (c >= Len(queue))
          /\  (capacity' = c)))
     /\  (UNCHANGED <<queue, active, crashed>>))

\* The spooler crashes silently and stops starting new prints.
Crash ==
    ( (~crashed)
     /\  (crashed' = TRUE)
     /\  (UNCHANGED <<queue, capacity, active>>))

\* While crashed, spooled jobs are flushed to relieve the full queue.
FlushOnCrash ==
    ( (crashed)
     /\  (Len(queue) > 0)
     /\  (queue' = Tail(queue))
     /\  (UNCHANGED <<capacity, active, crashed>>))

Next == Enqueue \/ StartPrint \/ FinishPrint \/ Reconfigure \/ Crash \/ FlushOnCrash

vars == <<queue, capacity, active, crashed>>
Init ==
    ( (queue = <<>>)
     /\  (capacity = 2)
     /\  (active = 0)
     /\  (crashed = FALSE))

Spec == Init /\ [][Next]_vars

\* Bounded capacity is never exceeded: the spool queue never holds more than its
\* current capacity, and no more printers are ever busy than physically exist.
CapacityRespected ==
    ( (Len(queue) <= capacity)
     /\  (active <= Printers))
====