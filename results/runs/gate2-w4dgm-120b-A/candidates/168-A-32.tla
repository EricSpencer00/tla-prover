---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

RingSize == NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

n == RingSize

TypeOK ==
  /\ readers \subseteq 1..n
  /\ writers \subseteq 1..n
  /\ queue \in Seq([pid: 1..n, mode: {"r", "w"}])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(i) ==
  /\ ~ \E k \in 1..Len(queue): queue[k].pid = i /\ queue[k].mode = "r"
  /\ queue' = Append(queue, [pid |-> i, mode |-> "r"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(i) ==
  /\ ~ \E k \in 1..Len(queue): queue[k].pid = i /\ queue[k].mode = "w"
  /\ queue' = Append(queue, [pid |-> i, mode |-> "w"])
  /\ UNCHANGED <<readers, writers>>

BeginRW ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET r == Head(queue) IN
       IF r.mode = "r" THEN
         /\ readers' = readers \cup {r.pid}
         /\ queue' = Tail(queue)
         /\ UNCHANGED writers
       ELSE
         /\ readers = {}
         /\ writers' = writers \cup {r.pid}
         /\ queue' = Tail(queue)
         /\ UNCHANGED readers
  /\ UNCHANGED <<>>

StopActivity(i) ==
  \/ readers' = readers \ {i}
  \/ writers' = writers \ {i}
  /\ UNCHANGED queue

Next ==
  \/ \E i \in 1..n: RequestRead(i)
  \/ \E i \in 1..n: RequestWrite(i)
  \/ BeginRW
  \/ \E i \in 1..n: StopActivity(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..n: SF_vars(RequestRead(i))
  /\ \A i \in 1..n: SF_vars(RequestWrite(i))
  /\ SF_vars(BeginRW)
  /\ \A i \in 1..n: WF_vars(StopActivity(i))

Safety ==
  /\ (writers # {}) => (readers = {})
  /\ \A i \in writers, j \in writers: i = j

Liveness ==
  /\ \A i \in 1..n: (i \in readers) ~> (i \notin readers)
  /\ \A i \in 1..n: (i \in writers) ~> (i \notin writers)

====