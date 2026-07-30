---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS
  NumActors

VARIABLES
  readers,
  writers,
  queue

vars == <<readers, writers, queue>>

\* An access request: a process, and the mode it wants (read or write).
Req == [pa : 0..(NumActors - 1), mode : {"read", "write"}]

TypeOK ==
  /\ readers \subseteq (0..(NumActors - 1))
  /\ writers \subseteq (0..(NumActors - 1))
  /\ queue \in Seq(Req)

\* Readers and writers are mutually exclusive, and writers are mutually exclusive.
Safety ==
  /\ readers \cap writers = {}
  /\ Cardinality(writers) <= 1

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process not already waiting to read joins the end of the queue.
RequestRead ==
  /\ Len(queue) < 2
  /\ ~ \E i \in DOMAIN queue : queue[i].pa = n /\ queue[i].mode = "read"
  /\ queue' = Append(queue, [pa |-> n, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process not already waiting to write joins the end of the queue.
RequestWrite ==
  /\ Len(queue) < 2
  /\ ~ \E i \in DOMAIN queue : queue[i].pa = n /\ queue[i].mode = "write"
  /\ queue' = Append(queue, [pa |-> n, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The front of the queue begins activity when it can: reads always, writes when nobody reads.
BeginAccess ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET r == Head(queue) IN
       /\ IF r.mode = "read"
          THEN readers' = readers \cup {r.pa}
          ELSE IF readers = {}
               THEN writers' = writers \cup {r.pa}
               ELSE UNCHANGED readers
       /\ queue' = Tail(queue)
  /\ UNCHANGED readers

StopActivity ==
  /\ \/ \E p \in readers : readers' = readers \ {p} /\ UNCHANGED writers
     \/ \E p \in writers : writers' = writers \ {p} /\ UNCHANGED readers
  /\ UNCHANGED queue

Next ==
  \/ RequestRead
  \/ RequestWrite
  \/ BeginAccess
  \/ StopActivity

Spec == Init /\ [][Next]_vars
        /\ WF_vars(RequestRead)
        /\ WF_vars(RequestWrite)
        /\ WF_vars(BeginAccess)
        /\ WF_vars(StopActivity)

\* Every process eventually gets to read.
Liveness == \A p \in 0..(NumActors - 1) : <>(p \in readers) /\ <>(p \in writers)

====