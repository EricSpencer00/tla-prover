---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS
  NumActors

\* "n" is used as the constant bound on actor identities inside the spec; the .cfg
\* file substitutes it for NumActors so that the model can be instantiated with any
\* finite number of actors. Every actor is addressed as an integer in 1..n.
n == NumActors

Processes == 1..n
ReqKinds == {"read", "write"}

VARIABLES
  readers,
  writers,
  queue

vars == << readers, writers, queue >>

TypeOK ==
  /\ readers \subseteq Processes
  /\ writers \subseteq Processes
  /\ queue \in Seq([kind : ReqKinds, who : Processes])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process may only be waiting in the queue if it is not already active in any
\* capacity; this prevents the same actor from holding two queued requests.
AlreadyQueued(p) ==
  \E i \in DOMAIN queue : queue[i].who = p

RequestRead(p) ==
  /\ ~AlreadyQueued(p)
  /\ ~ (p \in readers \/ p \in writers)
  /\ queue' = Append(queue, [kind |-> "read", who |-> p])
  /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
  /\ ~AlreadyQueued(p)
  /\ ~ (p \in readers \/ p \in writers)
  /\ queue' = Append(queue, [kind |-> "write", who |-> p])
  /\ UNCHANGED << readers, writers >>

\* The head of the queue is admitted only when it would not violate the
\* readers-writers mutual exclusion rule.
BeginServe ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ IF req.kind = "read" THEN
            /\ readers' = readers \cup {req.who}
            /\ writers' = writers
          ELSE
            /\ readers = {}
            /\ writers' = writers \cup {req.who}
            /\ readers' = readers
       /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in readers
     /\ readers' = readers \ {p}
     /\ writers' = writers
  /\ \/ p \in writers
     /\ writers' = writers \ {p}
     /\ readers' = readers
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p)
  \/ \E p \in Processes : RequestWrite(p)
  \/ BeginServe
  \/ \E p \in Processes : StopActivity(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in Processes : RequestRead(p))
        /\ WF_vars(\E p \in Processes : RequestWrite(p))
        /\ WF_vars(BeginServe)
        /\ WF_vars(\E p \in Processes : StopActivity(p))

\* Readers and writers are never active at the same time. Also, because writers is
\* a set of processes rather than a single slot, a second safety condition is
\* needed to forbid two writers from acting concurrently.
Safety ==
  /\ readers \cap writers = {}
  /\ \A p1, p2 \in writers : p1 = p2

Liveness ==
  /\ \A p \in Processes : (p \in readers) ~> (p \in writers)
  /\ \A p \in Processes : (p \in writers) ~> (p \in readers)
  /\ \A p \in Processes : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Processes : (p \in writers) ~> (p \notin writers)

====