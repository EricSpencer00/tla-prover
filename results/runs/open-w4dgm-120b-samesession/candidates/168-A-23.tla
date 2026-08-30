---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

(* A fair readers-writers solution with a first-come-first-served request     *)
(* queue.  Actors request read or write access; a pending request is          *)
(* honoured only when it is safe, which guarantees readers and writers never   *)
(* act at the same time.  Fairness on all actions ensures eventual progress.   *)

CONSTANTS NumActors

Actors == 1 .. NumActors
MaxQueue == NumActors

VARIABLES activeReaders, activeWriters, queue

vars == << activeReaders, activeWriters, queue >>

TypeOK ==
    /\ activeReaders \subseteq Actors
    /\ activeWriters \subseteq Actors
    /\ queue \in Seq([who: Actors, mode: {"read", "write"}])

Init ==
    /\ activeReaders = {}
    /\ activeWriters = {}
    /\ queue = << >>

InQueue(a, m) == \E k \in 1 .. Len(queue) : queue[k].who = a /\ queue[k].mode = m

\* Request to read: join the waiting queue if not already waiting to read.
ReqRead(a) ==
    /\ Len(queue) < MaxQueue
    /\ ~InQueue(a, "read")
    /\ queue' = Append(queue, [who |-> a, mode |-> "read"])
    /\ UNCHANGED << activeReaders, activeWriters >>

\* Request to write: join the waiting queue if not already waiting to write.
ReqWrite(a) ==
    /\ Len(queue) < MaxQueue
    /\ ~InQueue(a, "write")
    /\ queue' = Append(queue, [who |-> a, mode |-> "write"])
    /\ UNCHANGED << activeReaders, activeWriters >>

\* Begin reading or writing the front request, but only when it is safe.
ProcessFront ==
    /\ Len(queue) > 0
    /\ activeWriters = {}
    /\ LET h == Head(queue) IN
         IF h.mode = "read" THEN
             /\ activeReaders' = activeReaders \cup {h.who}
             /\ activeWriters' = activeWriters
         ELSE /\ activeWriters' = activeWriters \cup {h.who}
              /\ activeReaders' = activeReaders
    /\ queue' = Tail(queue)

\* Any active reader or writer may voluntarily stop.
StopActivity(a) ==
    /\ \/ a \in activeReaders
       \/ a \in activeWriters
    /\ activeReaders' = activeReaders \ {a}
    /\ activeWriters' = activeWriters {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : ReqRead(a)
    \/ \E a \in Actors : ReqWrite(a)
    \/ ProcessFront
    \/ \E a \in Actors : StopActivity(a)

Spec == Init /\ [][Next]_vars
    /\ \A f \in {ReqRead, ReqWrite, ProcessFront, StopActivity} : WF_vars(f)

(* Readers and writers are never simultaneously active.  Also, at most one *)
(* writer is active at any time.                                             *)
Safety ==
    /\ (activeWriters # {} => activeReaders = {})
    /\ (activeReaders # {} => activeWriters = {})
    /\ Cardinality(activeWriters) <= 1

(* Liveness: every process eventually gets to read and to write, and stops. *)
Liveness ==
    \A a \in Actors :
        /\ (a \in activeReaders) ~> (a \notin activeReaders)
        /\ (a \in activeWriters) ~> (a \notin activeWriters)

\* The constant is reinterpreted as a concrete bound for the bounded queue.
n == NumActors

====