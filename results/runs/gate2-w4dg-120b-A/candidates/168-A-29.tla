---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Procs == 1 .. NumActors
Opts == { "read", "write" }

VARIABLES readers, writers, queue
vars == << readers, writers, queue >>

QueueReq == [proc : Procs, opt : Opts]

TypeOK ==
  /\ readers \subseteq Procs
  /\ writers \subseteq Procs
  /\ queue \in Seq(QueueReq)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process that is not already waiting joins the end of the waiting queue
\* with a read request.
RequestRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, opt |-> "read"])
  /\ UNCHANGED << readers, writers >>

\* A process that is not already waiting joins the end of the waiting queue
\* with a write request.
RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, opt |-> "write"])
  /\ UNCHANGED << readers, writers >>

\* The front of the queue begins its access when it does not conflict with an
\* active writer (for reads) or an active reader (for writes).
ProcessQueue ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET front == Head(queue) IN
       IF front.opt = "read" THEN
         /\ readers' = readers \cup {front.proc}
         /\ writers' = writers
       ELSE
         /\ readers' = readers
         /\ writers' = IF readers = {} THEN writers \cup {front.proc} ELSE writers
     /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Procs : RequestRead(p)
  \/ \E p \in Procs : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in Procs : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Procs : RequestRead(p))
  /\ WF_vars(\E p \in Procs : RequestWrite(p))
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(\E p \in Procs : StopActivity(p))

\* Readers and writers are never simultaneously active; also at most one writer.
Safety ==
  /\ (writers # {} => readers = {})
  /\ (\A a \in writers, b \in writers : a = b)

Liveness ==
  /\ \A p \in Procs : <>(p \in readers)
  /\ \A p \in Procs : <>(p \in writers)
  /\ \A p \in Procs : <>(p \notin readers)
  /\ \A p \in Procs : <>(p \notin writers)

====