---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* n is the bounded analogue of NumActors used by the .cfg; it must be
\* defined in the module so the config's substitution succeeds.
n == NumActors

Actors == 1..NumActors
Requests == [act : {"read", "write"}, who : Actors]

VARIABLES activeReaders, activeWriters, queue

vars == <<activeReaders, activeWriters, queue>>

TypeOK ==
  /\ activeReaders \subseteq Actors
  /\ activeWriters \subseteq Actors
  /\ activeReaders \cap activeWriters = {}
  /\ queue \in Seq(Requests)

Init ==
  /\ activeReaders = {}
  /\ activeWriters = {}
  /\ queue = << >>

\* Request to read (enqueue at the back).
RequestRead(p) ==
  /\ \A k \in 1..Len(queue) : ~(queue[k].who = p /\ queue[k].act = "read")
  /\ queue' = Append(queue, [act |-> "read", who |-> p])
  /\ UNCHANGED <<activeReaders, activeWriters>>

\* Request to write (enqueue at the back).
RequestWrite(p) ==
  /\ \A k \in 1..Len(queue) : ~(queue[k].who = p /\ queue[k].act = "write")
  /\ queue' = Append(queue, [act |-> "write", who |-> p])
  /\ UNCHANGED <<activeReaders, activeWriters>>

\* Begin the request at the front of the queue under the readers-writers
\* rule (no writer while readers are active, and vice versa).
Begin ==
  /\ queue # << >>
  /\ activeWriters = {}
  /\ LET h == Head(queue) IN
       /\ IF h.act = "read" THEN
            /\ activeWriters = {}
            /\ activeReaders' = activeReaders \cup {h.who}
          ELSE
            /\ activeReaders = {}
            /\ activeWriters' = activeWriters \cup {h.who}
       /\ queue' = Tail(queue)

Stop(p) ==
  /\ \/ p \in activeReaders
     \/ p \in activeWriters
  /\ activeReaders' = IF p \in activeReaders THEN activeReaders \ {p} ELSE activeReaders
  /\ activeWriters' = IF p \in activeWriters THEN activeWriters \ {p} ELSE activeWriters
  /\ UNCHANGED queue

Next ==
  \E p \in Actors :
    \/ RequestRead(p) \/ RequestWrite(p) \/ Stop(p)
    \/ Begin

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in Actors : RequestRead(p))
        /\ WF_vars(\E p \in Actors : RequestWrite(p))
        /\ WF_vars(Begin)
        /\ WF_vars(\E p \in Actors : Stop(p))

\* No simultaneous readers and writers; at most one writer.
Safety ==
  /\ (activeWriters # {} => activeReaders = {})
  /\ (\A p \in Actors : p \in activeWriters => activeWriters = {p})

\* Every process eventually gets to read, write, and stop both.
Liveness ==
  /\ \A p \in Actors : (p \in activeReaders) ~> (p \notin activeReaders)
  /\ \A p \in Actors : (p \in activeWriters) ~> (p \notin activeWriters)
  /\ \A p \in Actors : (p \notin activeReaders) ~> (p \in activeReaders)
  /\ \A p \in Actors : (p \notin activeWriters) ~> (p \in activeWriters)

====