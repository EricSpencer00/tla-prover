---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Requests == [pid : NumActors, kind : {"R", "W"}]

TypeOK ==
    /\ readers \subseteq NumActors
    /\ writers \subseteq NumActors
    /\ queue \in Seq(Requests)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

\* Reader requests are queued, not granted immediately.
ReqRead(p) ==
    /\ ~\E i \in DOMAIN queue : queue[i].pid = p /\ queue[i].kind = "R"
    /\ queue' = Append(queue, [pid |-> p, kind |-> "R"])
    /\ UNCHANGED <<readers, writers>>

\* Writer requests are queued alongside readers.
ReqWrite(p) ==
    /\ ~\E i \in DOMAIN queue : queue[i].pid = p /\ queue[i].kind = "W"
    /\ queue' = Append(queue, [pid |-> p, kind |-> "W"])
    /\ UNCHANGED <<readers, writers>>

\* The head request begins its access when no writer currently holds the resource.
BeginAccess ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET r == Head(queue) IN
         /\ IF r.kind = "R"
            THEN readers' = readers \cup {r.pid}
            ELSE IF readers = {}
                 THEN writers' = writers \cup {r.pid}
                 ELSE UNCHANGED writers
            /\ queue' = Tail(queue)

StopActivity(p) ==
    \/ readers' = readers \ {p}
    \/ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in NumActors : ReqRead(p)
    \/ \E p \in NumActors : ReqWrite(p)
    \/ BeginAccess
    \/ \E p \in NumActors : StopActivity(p)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in NumActors : ReqRead(p))
    /\ WF_vars(\E p \in NumActors : ReqWrite(p))
    /\ WF_vars(BeginAccess)
    /\ WF_vars(\E p \in NumActors : StopActivity(p))

\* Readers and writers never run at the same time, and at most one writer.
Safety ==
    /\ (writers # {} => readers = {})
    /\ (writers = {} \/ writers = {Head(writers)})

\* Every actor eventually gets to read, writes, and finishes each.
Liveness ==
    \A p \in NumActors :
        /\ (p \in readers) ~> (p \notin readers)
        /\ (p \in writers) ~> (p \notin writers)

\* .cfg substitution: the system size bound (a finite concrete value).
n == 3

====