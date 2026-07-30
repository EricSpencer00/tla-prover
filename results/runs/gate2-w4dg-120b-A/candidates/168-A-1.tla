---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Procs == 1 .. NumActors

Modes == {"read", "write"}

VARIABLES activeReaders, activeWriters, queue
vars == <<activeReaders, activeWriters, queue>>

Reqs == [mode : Modes, id : Procs]

InQueue(id) == \E i \in 1 .. Len(queue) : queue[i].id = id

TypeOK ==
  /\ activeReaders \subseteq Procs
  /\ activeWriters \subseteq Procs
  /\ queue \in Seq(Reqs)

Init ==
  /\ activeReaders = {}
  /\ activeWriters = {}
  /\ queue = << >>

RequestRead(p) ==
  /\ ~InQueue(p)
  /\ queue' = Append(queue, [mode |-> "read", id |-> p])
  /\ UNCHANGED <<activeReaders, activeWriters>>

RequestWrite(p) ==
  /\ ~InQueue(p)
  /\ queue' = Append(queue, [mode |-> "write", id |-> p])
  /\ UNCHANGED <<activeReaders, activeWriters>>

BeginService ==
  /\ Len(queue) > 0
  /\ activeWriters = {}
  /\ LET r == Head(queue) IN
       /\ IF r.mode = "read" THEN
            /\ activeReaders' = activeReaders \cup {r.id}
            /\ activeWriters' = activeWriters
          ELSE
            /\ IF activeReaders = {} THEN
                 activeWriters' = activeWriters \cup {r.id}
               ELSE
                 activeWriters' = activeWriters
               /\ activeReaders' = activeReaders
          /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in activeReaders
     \/ p \in activeWriters
  /\ activeReaders' = activeReaders \ {p}
  /\ activeWriters' = activeWriters \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Procs : RequestRead(p)
  \/ \E p \in Procs : RequestWrite(p)
  \/ BeginService
  \/ \E p \in Procs : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs : WF_vars(RequestRead(p))
  /\ \A p \in Procs : WF_vars(RequestWrite(p))
  /\ WF_vars(BeginService)
  /\ \A p \in Procs : WF_vars(StopActivity(p))

Safety ==
  /\ (activeWriters = {} \/ activeReaders = {})
  /\ Cardinality(activeWriters) <= 1

Liveness ==
  /\ \A p \in Procs : (p \in activeReaders) ~> (p \notin activeReaders)
  /\ \A p \in Procs : (p \in activeWriters) ~> (p \notin activeWriters)

====