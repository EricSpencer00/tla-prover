---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Processes == 1..NumActors

Requests == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Waiting == {queue[i].proc : i \in DOMAIN queue}

TypeOK ==
    /\ readers \subseteq Processes
    /\ writers \subseteq Processes
    /\ queue \in Seq([kind: Requests, proc: Processes])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ p \notin Waiting
    /\ queue' = Append(queue, [kind |-> "read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \notin Waiting
    /\ queue' = Append(queue, [kind |-> "write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET front == Head(queue) IN
        /\ IF front.kind = "read" THEN
            readers' = readers \cup {front.proc}
           ELSE
            /\ readers = {}
            writers' = writers \cup {front.proc}
        /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Processes : RequestRead(p)
    \/ \E p \in Processes : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Processes : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Processes : RequestRead(p))
    /\ WF_vars(\E p \in Processes : RequestWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(\E p \in Processes : StopActivity(p))

Safety ==
    /\ readers = {} \/ writers = {}
    /\ writers \subseteq Processes
    /\ \A a, b \in writers : a = b

Liveness ==
    /\ \A p \in Processes : (p \in readers) ~> (p \notin readers)
    /\ \A p \in Processes : (p \in writers) ~> (p \notin writers)

====