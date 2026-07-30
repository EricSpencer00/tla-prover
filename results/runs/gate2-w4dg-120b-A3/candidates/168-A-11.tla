---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES readerSet, writerSet, queue
vars == <<readerSet, writerSet, queue>>

ReqTypes == {"read", "write"}
Requests == [type : ReqTypes, proc : 1..NumActors]

TypeOK ==
  /\ readerSet \subseteq (1..NumActors)
  /\ writerSet \subseteq (1..NumActors)
  /\ queue \in Seq(Requests)

Init ==
  /\ readerSet = {}
  /\ writerSet = {}
  /\ queue = << >>

EnqueueReq(rt, p) ==
  /\ Len(queue) < 3
  /\ queue' = Append(queue, [type |-> rt, proc |-> p])
  /\ UNCHANGED <<readerSet, writerSet>>

RequestRead(p) == EnqueueReq("read", p)
RequestWrite(p) == EnqueueReq("write", p)

BeginServe ==
  /\ queue # << >>
  /\ writerSet = {}
  /\ LET front == Head(queue) IN
       /\ \/ (front.type = "read") /\ readerSet' = readerSet \cup {front.proc}
          \/ (front.type = "write" /\ readerSet = {})
               /\ writerSet' = writerSet \cup {front.proc}
       /\ queue' = Tail(queue)
  /\ UNCHANGED <<>>

StopActivity(p) ==
  \/ /\ p \in readerSet
     /\ readerSet' = readerSet \ {p}
     /\ UNCHANGED <<writerSet, queue>>
  \/ /\ p \in writerSet
     /\ writerSet' = writerSet \ {p}
     /\ UNCHANGED <<readerSet, queue>>

Next ==
  \/ \E p \in 1..NumActors : RequestRead(p)
  \/ \E p \in 1..NumActors : RequestWrite(p)
  \/ BeginServe
  \/ \E p \in 1..NumActors : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..NumActors : RequestRead(p))
  /\ WF_vars(\E p \in 1..NumActors : RequestWrite(p))

\* SAFETY PROPERTY: readers and writers are never active at the same time.
MutualExclusion ==
  /\ (writerSet # {}) => (readerSet = {})
  /\ (readerSet # {}) => (writerSet = {})

\* LIVENESS PROPERTY: every process eventually reads and eventually writes.
Liveness ==
  \A p \in 1..NumActors :
    /\ (p \in readerSet) ~> (p \notin readerSet)
    /\ (p \in writerSet) ~> (p \notin writerSet)

n == NumActors
====