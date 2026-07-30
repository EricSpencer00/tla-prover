---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences

\* A fair readers-writers solution using a first-come-first-served queue. The
\* queue orders access requests, and weak fairness on every action prevents
\* starvation of either readers or writers.
CONSTANTS NumActors

Processes == 1..NumActors
Modes == {"read", "write"}
MaxQueue == NumActors

VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

TypeOK ==
  /\ readers \subseteq Processes
  /\ writers \subseteq Processes
  /\ queue \in Seq([who : Processes, mode : Modes])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process that is not already queued may request read access.
RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p
  /\ Len(queue) < MaxQueue
  /\ queue' = Append(queue, [who |-> p, mode |-> "read"])
  /\ UNCHANGED << readers, writers >>

\* A process that is not already queued may request write access.
RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p
  /\ Len(queue) < MaxQueue
  /\ queue' = Append(queue, [who |-> p, mode |-> "write"])
  /\ UNCHANGED << readers, writers >>

\* The queue head is granted when its mode is compatible with the current activity.
BeginAccess ==
  /\ queue # << >>
  /\ writers = {}
  /\ IF Head(queue).mode = "read"
       THEN readers' = readers \cup {Head(queue).who}
            /\ writers' = writers
            /\ queue' = Tail(queue)
       ELSE /\ readers = {}
            /\ writers' = writers \cup {Head(queue).who}
            /\ queue' = Tail(queue)

\* Any active participant may stop, freeing the resource.
StopActivity(p) ==
  /\ (p \in readers \/ p \in writers)
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p)
  \/ \E p \in Processes : RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in Processes : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes : RequestRead(p))
  /\ WF_vars(\E p \in Processes : RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ \A p \in Processes : WF_vars(StopActivity(p))

\* Readers and writers are never active at the same time.
Safety ==
  /\ ~(readers # {} /\ writers # {})
  /\ Cardinality(writers) <= 1

\* Every process eventually gets to read, and eventually gets to write.
Liveness ==
  \A p \in Processes :
    /\ (p \in readers) ~> (p \in writers)
    /\ (p \in writers) ~> (p \in readers)

====