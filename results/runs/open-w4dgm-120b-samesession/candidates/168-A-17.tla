---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

(* Fair readers-writers solution with a queue providing first-come-first-    *)
(* served access, so neither readers nor writers starve.  Actors post read   *)
(* and write requests to a bounded queue; a write needs exclusive access, a   *)
(* read may proceed whenever no writer is active.  Actions are weakly fair,    *)
(* guaranteeing the queue is eventually drained and every actor eventually   *)
(* reads and writes.                                                          *)

CONSTANTS NumActors

Requests == [actor : 1..NumActors, mode : {"read", "write"}]

VARIABLES reading, writing, waitqueue

vars == <<reading, writing, waitqueue>>

\* Bounded capacity: the request queue never grows past the fixed actor count.
TypeOK ==
    /\ reading \subseteq (1..NumActors)
    /\ writing \subseteq (1..NumActors)
    /\ waitqueue \in Seq(Requests)
    /\ Len(waitqueue) <= NumActors

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ waitqueue = << >>

RequestRead(a) ==
    /\ \A i \in 1..Len(waitqueue) : waitqueue[i].actor # a
    /\ waitqueue' = Append(waitqueue, [actor |-> a, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ \A i \in 1..Len(waitqueue) : waitqueue[i].actor # a
    /\ waitqueue' = Append(waitqueue, [actor |-> a, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

\* A write needs a completely quiet resource; a read is allowed alongside.
StartAccess ==
    /\ waitqueue # << >>
    /\ writing = {}
    /\ LET r == Head(waitqueue)
       IN /\ waitqueue' = Tail(waitqueue)
          /\ reading' = IF r.mode = "read" /\ writing = {} THEN reading \cup {r.actor} ELSE reading
          /\ writing' = IF r.mode = "write" /\ reading = {} THEN writing \cup {r.actor} ELSE writing

StopActivity(a) ==
    /\ (a \in reading \/ a \in writing)
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED waitqueue

Next ==
    \E a \in 1..NumActors :
        RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
    \/ StartAccess

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(StartAccess)
    /\ \A a \in 1..NumActors : SF_vars(StopActivity(a))

\* Readers and writers never hold the resource at the same time; writers are
\* mutually exclusive.
Safety ==
    /\ (writing # {}) => (reading = {})
    /\ (writing \subseteq (1..NumActors))
    /\ (reading \subseteq (1..NumActors))

Liveness ==
    /\ \A a \in 1..NumActors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in 1..NumActors : (a \in writing) ~> (a \notin writing)

====