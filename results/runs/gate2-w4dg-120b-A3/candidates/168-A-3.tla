---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors > 0

Actors == 1 .. NumActors
Modes == {"read", "write"}
QueueMax == 2

VARIABLES readers, writers, queue
vars == << readers, writers, queue >>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([actor: Actors, mode: Modes])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(p) ==
  /\ p \notin readers
  /\ p \notin writers
  /\ ~ \E i \in 1 .. Len(queue) : queue[i].actor = p /\ queue[i].mode = "read"
  /\ Len(queue) < QueueMax
  /\ queue' = Append(queue, [actor |-> p, mode |-> "read"])
  /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
  /\ p \notin readers
  /\ p \notin writers
  /\ ~ \E i \in 1 .. Len(queue) : queue[i].actor = p /\ queue[i].mode = "write"
  /\ Len(queue) < QueueMax
  /\ queue' = Append(queue, [actor |-> p, mode |-> "write"])
  /\ UNCHANGED << readers, writers >>

StartAccess ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF req.mode = "read" THEN readers' = readers \cup {req.actor} /\ writers' = writers
          ELSE IF readers = {} THEN writers' = writers \cup {req.actor} /\ readers' = readers
               ELSE readers' = readers /\ writers' = writers

StopActivity(p) ==
  /\ p \in readers \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED << queue >>

Next ==
  \/ \E p \in Actors : RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)
  \/ StartAccess

Spec == Init /\ [][Next]_vars

Safety ==
  /\ (writers # {} => readers = {})
  /\ writers \subseteq Readers \cup Writers
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in Actors :
       /\ (p \in readers) ~> (p \notin readers)
       /\ (p \in writers) ~> (p \notin writers)

n == NumActors

====