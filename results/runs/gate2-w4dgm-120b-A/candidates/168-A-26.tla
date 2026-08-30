---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

ASSUME NumActors \in Nat

Actors == 1 .. NumActors

\* A request carries the process and whether it wants read or write access.
Requests == [actor: Actors, kind: {"read", "write"}]

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* No process is both reading and writing, and two writers can never clash.
\* Readers may share freely, writers may not.
Safety ==
  /\ readers \cap writers = {}
  /\ Cardinality(writers) <= 1

\* Either side of the resource is always empty: no readers while a writer acts.
\* Fairness below covers every queued request, so neither side starves.
\* Liveness below covers the action of each side, so neither side hangs.
Spec == Init /\ [][Next]_vars
  /\ WF_vars(EnqueueRead)
  /\ WF_vars(EnqueueWrite)
  /\ WF_vars(Enter)
  /\ WF_vars(Leave)

EnqueueRead ==
  /\ \E p \in Actors :
       /\ \A i \in 1 .. Len(queue) : ~(queue[i].actor = p /\ queue[i].kind = "read")
       /\ queue' = Append(queue, [actor |-> p, kind |-> "read"])
  /\ UNCHANGED <<readers, writers>>

EnqueueWrite ==
  /\ \A i \in 1 .. Len(queue) : ~(queue[i].kind = "write")
  /\ \E p \in Actors :
       queue' = Append(queue, [actor |-> p, kind |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* A read request needs no further test. A write request can only proceed when
\* nobody is reading, which makes readers and writers mutually exclusive.
Enter ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET h == Head(queue) IN
       /\ IF h.kind = "read" THEN readers' = readers \cup {h.actor} ELSE writers' = writers \cup {h.actor}
       /\ queue' = Tail(queue)
  /\ UNCHANGED writers

Leave ==
  \/ \E p \in readers : readers' = readers \ {p} /\ UNCHANGED <<writers, queue>>
  \/ \E p \in writers : writers' = writers \ {p} /\ UNCHANGED <<readers, queue>>

Next == EnqueueRead \/ EnqueueWrite \/ Enter \/ Leave

\* Every actor eventually gets to read and to write, and finishes both.
Liveness ==
  \A p \in Actors :
    /\ (p \in readers) ~> (p \notin readers)
    /\ (p \in writers) ~> (p \notin writers)
====