---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Every process is a natural number below NumActors; the queue holds
\* the ordered requests that have not yet been granted.
Processes == 0..(NumActors - 1)
Modes == {"read", "write"}

VARIABLES readers, writers, queue
vars == << readers, writers, queue >>

TypeOK ==
  /\ readers \subseteq Processes
  /\ writers \subseteq Processes
  /\ queue \in Seq([proc: Processes, mode: Modes])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* Only one read request per process at a time is queued; a process that
\* already has a pending request is not queued a second time.
RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, mode |-> "read"])
  /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, mode |-> "write"])
  /\ UNCHANGED << readers, writers >>

\* The queue is processed strictly from the front. Readers may start
\* whenever nothing is writing; a writer may start only when nothing
\* is reading already, which enforces the readers-writer alternation.
BeginAccess ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ req.mode = "read" => readers' = readers \cup {req.proc}
       /\ req.mode = "write" => (readers = {}) /\ writers' = writers \cup {req.proc}
       /\ queue' = Tail(queue)
  /\ UNCHANGED readers
  /\ UNCHANGED writers

\* Active participants always get a chance to stop, which is what lets
\* the next queued request make progress.
StopActivity(p) ==
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p)
  \/ \E p \in Processes : RequestWrite(p)
  \/ \E p \in Processes : StopActivity(p)
  \/ BeginAccess

Fairness ==
  /\ \A p \in Processes : WF_vars(RequestRead(p))
  /\ \A p \in Processes : WF_vars(RequestWrite(p))
  /\ \A p \in Processes : WF_vars(StopActivity(p))
  /\ WF_vars(BeginAccess)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Correctness: readers and writers are mutually exclusive, and writers
\* never exceed a single concurrent writer.
Safety ==
  /\ writers = {} => readers \cap writers = {}
  /\ writers # {} => readers = {}
  /\ \A a, b \in writers : a = b

\* Liveness: everyone gets a turn at both reading and writing.
Liveness ==
  /\ \A p \in Processes : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Processes : (p \in writers) ~> (p \notin writers)

====