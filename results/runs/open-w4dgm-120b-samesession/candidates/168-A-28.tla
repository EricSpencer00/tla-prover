---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat

Reading == "reading"
Writing == "writing"
NoR == "none"
NoW == "none"

Access == {Reading, Writing}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(p) ==
  /\ Len(queue) < NumActors
  /\ ~ \E k \in DOMAIN queue : queue[k].actor = p
  /\ queue' = Append(queue, [type |-> Reading, actor |-> p])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ Len(queue) < NumActors
  /\ ~ \E k \in DOMAIN queue : queue[k].actor = p
  /\ queue' = Append(queue, [type |-> Writing, actor |-> p])
  /\ UNCHANGED <<readers, writers>>

BeginAccess ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       /\ IF h.type = Reading
          THEN readers' = readers \cup {h.actor}
          ELSE IF readers = {} THEN writers' = writers \cup {h.actor} ELSE readers' = readers
       /\ queue' = Tail(queue)
       /\ UNCHANGED writers
       \/ UNCHANGED writers

StopActivity(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in 1..NumActors : RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)
  \/ BeginAccess

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..NumActors : RequestRead(p))
  /\ WF_vars(\E p \in 1..NumActors : RequestWrite(p))
  /\ WF_vars(\E p \in 1..NumActors : StopActivity(p))

TypeOK ==
  /\ readers \subseteq 1..NumActors
  /\ writers \subseteq 1..NumActors
  /\ Len(queue) <= NumActors

Safety ==
  /\ (writers # {} => readers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ (\A p \in 1..NumActors : (p \in readers) ~> (p \notin readers))
  /\ (\A p \in 1..NumActors : (p \in writers) ~> (p \notin writers))

n == 3
====