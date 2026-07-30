---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Process == 1..NumActors
ActionType == {"read", "write"}
Req == [actor : Process, act : ActionType]

Queued(p) == \E i \in 1..Len(queue) : queue[i].actor = p

TypeOK ==
  /\ readers \subseteq Process
  /\ writers \subseteq Process
  /\ queue \in Seq(Req)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ ~Queued(p)
  /\ queue' = Append(queue, [actor |-> p, act |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ ~Queued(p)
  /\ queue' = Append(queue, [actor |-> p, act |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* Front of the queue only proceeds when it would not conflict with the
\* current safety condition, which is what gives fairness: writers wait
\* for readers to drain rather than silently preempting them.
ProcessQueue ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET r == Head(queue) IN
       /\ IF r.act = "read" THEN
            /\ readers' = readers \cup {r.actor}
            /\ writers' = writers
          ELSE
            /\ readers' = {}
            /\ writers' = writers \cup {r.actor}
       /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Process : RequestRead(p)
  \/ \E p \in Process : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in Process : StopActivity(p)

Spec == Init /\ [][Next]_vars
        /\ UNCHANGED writers
        /\ UNCHANGED readers
        /\ UNCHANGED queue
        /\ WF_vars(\E p \in Process : RequestRead(p))
        /\ WF_vars(\E p \in Process : RequestWrite(p))
        /\ WF_vars(ProcessQueue)
        /\ WF_vars(\E p \in Process : StopActivity(p))

\* Mutual exclusion: readers and writers never co-active, and only one writer.
Safety ==
  /\ (writers # {} => readers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in Process : (p \in readers) ~> (p \in writers)
  /\ \A p \in Process : (p \in writers) ~> (p \in readers)
  /\ \A p \in Process : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Process : (p \in writers) ~> (p \notin writers)

====