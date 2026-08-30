---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

(* Readers-writers access to a shared resource, with writers given exclusive   *)
(* access by a first-come-first-served request queue.  A process may request a *)
(* read or a write; the queue is processed in order.  When a write is active,    *)
(* no reads are active and vice versa, and at most one writer is ever active.   *)

CONSTANTS NumActors

Actors == 1 .. NumActors

Mode == {"read", "write"}

VARIABLES reading, writing, queue

vars == << reading, writing, queue >>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq([who : Actors, mode : Mode])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

RequestRead(a) ==
    /\ ~ \E i \in 1 .. Len(queue) : queue[i].who = a /\ queue[i].mode = "read"
    /\ queue' = Append(queue, [who |-> a, mode |-> "read"])
    /\ UNCHANGED << reading, writing >>

RequestWrite(a) ==
    /\ ~ \E i \in 1 .. Len(queue) : queue[i].who = a /\ queue[i].mode = "write"
    /\ queue' = Append(queue, [who |-> a, mode |-> "write"])
    /\ UNCHANGED << reading, writing >>

ProcessQueue ==
    /\ Len(queue) > 0
    /\ writing = {}
    /\ LET item == Head(queue) IN
        /\ queue' = Tail(queue)
        /\ IF item.mode = "read" THEN
              reading' = reading \cup {item.who}
           ELSE IF item.mode = "write" /\ reading = {} THEN
              writing' = writing \cup {item.who}
           ELSE
              reading' = reading
              writing' = writing
    /\ UNCHANGED << >>

StopActivity(a) ==
    \/ reading' = reading \ {a}
    \/ writing' = writing \ {a}
    /\ UNCHANGED << queue >>

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ ProcessQueue
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProcessQueue)
    /\ \A a \in Actors : SF_vars(RequestRead(a)) /\ SF_vars(RequestWrite(a)) /\ SF_vars(StopActivity(a))

(* Readers and writers are never active at the same time, and at most one      *)
(* writer is active at any moment.                                             *)
Safety ==
    /\ (writing # {} => reading = {})
    /\ \A a, b \in Actors : (a \in writing /\ b \in writing) => a = b

(* Every process eventually gets to read.                                      *)
ReadersEventuallyActive ==
    \A a \in Actors : <>(a \in reading)

(* Every process eventually gets to write.                                     *)
WritersEventuallyActive ==
    \A a \in Actors : <>(a \in writing)

(* Everything that becomes active eventually stops.                            *)
Liveness == ReadersEventuallyActive /\ WritersEventuallyActive

\* The .cfg substitutes `3' in the place of `NumActors' below.
n == 3

====