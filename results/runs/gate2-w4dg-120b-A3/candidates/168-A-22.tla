---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Queue entries record the requesting process together with the requested
\* mode (read vs. write); the queue is processed strictly in order.
VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

SomeReq == \E i \in 1 .. Len(queue) : queue[i]

TypeOK ==
  /\ reading \subseteq NumActors
  /\ writing \subseteq NumActors
  /\ reading \cap writing = {}
  /\ queue \in Seq([proc : NumActors, mode : {"read", "write"}])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

\* Every reader that wants a turn is placed on the (bounded) back of the queue.
RequestRead(p) ==
  /\ \A i \in 1 .. Len(queue) : queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, mode |-> "read"])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ \A i \in 1 .. Len(queue) : queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, mode |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The front of the queue is served only when it is safe to do so, which is
\* what enforces first-come-first-served fairness.
BeginAction ==
  /\ queue # << >>
  /\ writing = {}
  /\ LET h == Head(queue) IN
       /\ h.mode = "read"
       /\ reading' = reading \cup {h.proc}
       /\ queue' = Tail(queue)
       /\ UNCHANGED writing
       \/ /\ h.mode = "write"
          /\ reading = {}
          /\ writing' = {h.proc}
          /\ queue' = Tail(queue)
          /\ UNCHANGED reading

StopActivity(p) ==
  /\ \/ p \in reading
     \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in NumActors : RequestRead(p)
  \/ \E p \in NumActors : RequestWrite(p)
  \/ BeginAction
  \/ \E p \in NumActors : StopActivity(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in NumActors : RequestRead(p))
        /\ WF_vars(\E p \in NumActors : RequestWrite(p))
        /\ WF_vars(BeginAction)
        /\ WF_vars(\E p \in NumActors : StopActivity(p))

\* Readers and writers can never be active at the same moment, and no two
\* writers can hold the resource together.
Safety == reading = {} \/ writing = {}
          /\ \A a, b \in writing : a = b

Liveness ==
  /\ \A p \in NumActors : (p \in reading) ~> (p \notin reading)
  /\ \A p \in NumActors : (p \in writing) ~> (p \notin writing)
  /\ \A p \in NumActors : (p \in reading) ~> (p \in writing)
  /\ \A p \in NumActors : (p \in writing) ~> (p \in reading)

\* The .cfg file substitutes the concrete number of actors into the
\* symbolic name n this operator must therefore exist.
n == NumActors

====