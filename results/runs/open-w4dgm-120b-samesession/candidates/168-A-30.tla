---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ queue \in Seq([pid: NumActors, mode: {"read", "write"}])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead ==
  /\ \E p \in NumActors :
       /\ \A i \in DOMAIN queue : queue[i].pid # p
       /\ queue' = Append(queue, [pid |-> p, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite ==
  /\ \E p \in NumActors :
       /\ \A i \in DOMAIN queue : queue[i].pid # p
       /\ queue' = Append(queue, [pid |-> p, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

BeginReadWrite ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       \/ /\ h.mode = "read"
          /\ readers' = readers \cup {h.pid}
       \/ /\ h.mode = "write"
          /\ readers = {}
          /\ writers' = writers \cup {h.pid}
  /\ queue' = Tail(queue)
  /\ UNCHANGED <<readers, writers>>

StopActivity ==
  /\ \E p \in readers \cup writers :
       readers' = readers \ {p}
       /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ RequestRead
  \/ RequestWrite
  \/ BeginReadWrite
  \/ StopActivity

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead)
  /\ WF_vars(RequestWrite)
  /\ WF_vars(BeginReadWrite)
  /\ WF_vars(StopActivity)

Safety ==
  /\ (writers # {}) => (readers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in NumActors : (p \in readers) ~> (p \notin readers)
  /\ \A p \in NumActors : (p \in writers) ~> (p \notin writers)

====