---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Request == [pid: 1..NumActors, kind: {"r", "w"}]

TypeOK ==
  /\ readers \subseteq (1..NumActors)
  /\ writers \subseteq (1..NumActors)
  /\ queue \in Seq(Request)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process that is not already queued for that mode joins the wait queue.
RequestRead(i) ==
  /\ ~ \E k \in 1..Len(queue): queue[k].pid = i /\ queue[k].kind = "r"
  /\ queue' = Append(queue, [pid |-> i, kind |-> "r"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(i) ==
  /\ ~ \E k \in 1..Len(queue): queue[k].pid = i /\ queue[k].kind = "w"
  /\ queue' = Append(queue, [pid |-> i, kind |-> "w"])
  /\ UNCHANGED <<readers, writers>>

\* FCFS discipline: the head of the queue is serviced, and writers win only
\* when nobody is reading (exclusive access).
BeginIO ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       /\ IF h.kind = "r"
            THEN readers' = readers \cup {h.pid}
            ELSE /\ writers' = {h.pid}
                 /\ readers' = readers
       /\ queue' = Tail(queue)

StopActivity(i) ==
  /\ \/ i \in readers
     \/ i \in writers
  /\ readers' = readers \ {i}
  /\ writers' = writers \ {i}
  /\ UNCHANGED queue

Next ==
  \/ \E i \in 1..NumActors: RequestRead(i)
  \/ \E i \in 1..NumActors: RequestWrite(i)
  \/ BeginIO
  \/ \E i \in 1..NumActors: StopActivity(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..NumActors: RequestRead(i))
  /\ WF_vars(\E i \in 1..NumActors: RequestWrite(i))
  /\ WF_vars(BeginIO)
  /\ \A i \in 1..NumActors: WF_vars(StopActivity(i))

\* Readers and writers are mutually exclusive, and writers are exclusive among
\* themselves.
Safety ==
  /\ readers = {} \/ writers = {}
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A i \in 1..NumActors: <>(i \in readers)
  /\ \A i \in 1..NumActors: <>(i \in writers)
  /\ \A i \in 1..NumActors: (i \in readers) ~> (i \notin readers)
  /\ \A i \in 1..NumActors: (i \in writers) ~> (i \notin writers)

====