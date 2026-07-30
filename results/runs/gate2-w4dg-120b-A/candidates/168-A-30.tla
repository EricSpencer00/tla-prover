---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Processes == 1 .. NumActors

Modes == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq Processes
    /\ writers \subseteq Processes
    /\ queue \in Seq([mode : Modes, pid : Processes])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

InQueue(p) == \E i \in 1 .. Len(queue) : queue[i].pid = p

RequestRead(p) ==
    /\ ~InQueue(p)
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [mode |-> "read", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ ~InQueue(p)
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [mode |-> "write", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

BeginRW ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET head == Head(queue) IN
        /\ head.mode = "read"
            \/ (head.mode = "write" /\ readers = {})
        /\ readers' = IF head.mode = "read" THEN readers \cup {head.pid} ELSE readers
        /\ writers' = IF head.mode = "write" THEN writers \cup {head.pid} ELSE writers
    /\ queue' = Tail(queue)

StopRW(p) ==
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Processes : RequestRead(p)
    \/ \E p \in Processes : RequestWrite(p)
    \/ BeginRW
    \/ \E p \in Processes : StopRW(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in Processes : RequestRead(p))
        /\ WF_vars(\E p \in Processes : RequestWrite(p))
        /\ WF_vars(BeginRW)
        /\ WF_vars(\E p \in Processes : StopRW(p))

Safety ==
    /\ (writers # {} => readers = {})
    /\ \A a \in writers, b \in writers : a = b

Liveness ==
    /\ \A p \in Processes :
        /\ (p \in readers) ~> (p \notin readers)
        /\ (p \in writers) ~> (p \notin writers)
    /\ \A p \in Processes :
        /\ TRUE ~> (p \in readers)
        /\ TRUE ~> (p \in writers)

====