---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Kinds == {"read", "write"}
Requests == [kind: Kinds, proc: NumActors]

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(p) ==
  /\ \A i \in DOMAIN queue : ~(queue[i].proc = p /\ queue[i].kind = "read")
  /\ queue' = Append(queue, [kind |-> "read", proc |-> p])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : ~(queue[i].proc = p /\ queue[i].kind = "write")
  /\ queue' = Append(queue, [kind |-> "write", proc |-> p])
  /\ UNCHANGED <<readers, writers>>

BeginService ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       /\ IF h.kind = "read"
            THEN readers' = readers \cup {h.proc}
            ELSE /\ readers = {}
                 /\ writers' = writers \cup {h.proc}
       /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ (p \in readers \/ p \in writers)
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in NumActors : RequestRead(p)
  \/ \E p \in NumActors : RequestWrite(p)
  \/ BeginService
  \/ \E p \in NumActors : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in NumActors : WF_vars(RequestRead(p))
  /\ \A p \in NumActors : WF_vars(RequestWrite(p))
  /\ WF_vars(BeginService)
  /\ \A p \in NumActors : WF_vars(StopActivity(p))

Safety ==
  /\ (readers # {} => writers = {})
  /\ (\A p, q \in writers : p = q)

Liveness ==
  /\ \A p \in NumActors : (p \in readers) ~> (p \notin readers)
  /\ \A p \in NumActors : (p \in writers) ~> (p \notin writers)

InQueue(p) == \E i \in DOMAIN queue : queue[i].proc = p

n == Cardinality(NumActors)
====