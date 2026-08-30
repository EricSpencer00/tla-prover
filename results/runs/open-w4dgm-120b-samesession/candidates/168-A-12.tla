---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors >= 1

Actors == 1..NumActors

Modes == {"idle", "waiting", "reading", "writing"}

VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

Requests == [actor: Actors, mode: {"read", "write"}]

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead ==
  /\ \A i \in Actors : ~ \E k \in 1..Len(queue) : queue[k].actor = i /\ queue[k].mode = "read"
  /\ queue' = Append(queue, [actor |-> n, mode |-> "read"])
  /\ UNCHANGED << readers, writers >>

RequestWrite ==
  /\ \A i \in Actors : ~ \E k \in 1..Len(queue) : queue[k].actor = i /\ queue[k].mode = "write"
  /\ queue' = Append(queue, [actor |-> n, mode |-> "write"])
  /\ UNCHANGED << readers, writers >>

BeginAccess ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ IF req.mode = "read" THEN
            /\ readers' = readers \cup {req.actor}
            /\ writers' = writers
          ELSE
            /\ writers' = IF readers = {} THEN writers \cup {req.actor} ELSE writers
            /\ readers' = IF readers = {} THEN readers ELSE readers
       /\ queue' = Tail(queue)

StopActivity ==
  /\ \E i \in readers : readers' = readers \ {i} /\ UNCHANGED << writers, queue >>
  \/ \E i \in writers : writers' = writers \ {i} /\ UNCHANGED << readers, queue >>

Next ==
  \/ RequestRead
  \/ RequestWrite
  \/ BeginAccess
  \/ StopActivity

Spec == Init /\ [][Next]_vars
    /\ WF_vars(RequestRead) /\ WF_vars(RequestWrite)
    /\ WF_vars(BeginAccess) /\ WF_vars(StopActivity)

Safety ==
  /\ readers # {} => writers = {}
  /\ writers # {} => readers = {}
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ (\A i \in Actors : <>(i \in readers))
  /\ (\A i \in Actors : <>(i \in writers))
  /\ (\A i \in Actors : (i \in readers) ~> (i \notin readers))
  /\ (\A i \in Actors : (i \in writers) ~> (i \notin writers))

n == CHOOSE i \in Actors : TRUE

====