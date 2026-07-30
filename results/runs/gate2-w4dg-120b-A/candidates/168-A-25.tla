---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors > 0

Processes == 1 .. NumActors
Modes == {"read", "write"}

VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

TypeOK ==
    /\ readers \subseteq Processes
    /\ writers \subseteq Processes
    /\ queue \in Seq([actor: Processes, mode: Modes])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

Queued(pid, mode) == \E i \in 1 .. Len(queue) : queue[i].actor = pid /\ queue[i].mode = mode

RequestRead(pid) ==
    /\ ~Queued(pid, "read")
    /\ queue' = Append(queue, [actor |-> pid, mode |-> "read"])
    /\ UNCHANGED << readers, writers >>

RequestWrite(pid) ==
    /\ ~Queued(pid, "write")
    /\ queue' = Append(queue, [actor |-> pid, mode |-> "write"])
    /\ UNCHANGED << readers, writers >>

ProcessQueue ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET front == Head(queue) IN
        IF front.mode = "read" THEN
            /\ readers' = readers \cup {front.actor}
            /\ writers' = writers
            /\ queue' = Tail(queue)
        ELSE
            /\ readers = {}
            /\ writers' = writers \cup {front.actor}
            /\ queue' = Tail(queue)

StopActivity(pid) ==
    /\ \/ pid \in readers
       \/ pid \in writers
    /\ readers' = readers \ {pid}
    /\ writers' = writers \ {pid}
    /\ UNCHANGED queue

Next ==
    \/ \E pid \in Processes : RequestRead(pid)
    \/ \E pid \in Processes : RequestWrite(pid)
    \/ ProcessQueue
    \/ \E pid \in Processes : StopActivity(pid)

Spec == Init /\ [][Next]_vars

Safety ==
    /\ readers # {} => writers = {}
    /\ \A p, q \in writers : p = q

Liveness ==
    /\ \A pid \in Processes : (pid \in readers) ~> (pid \notin readers)
    /\ \A pid \in Processes : (pid \in writers) ~> (pid \notin writers)

====