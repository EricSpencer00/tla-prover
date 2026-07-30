---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Procs == 1..NumActors

Request == [typ : {"read", "write"}, proc : Procs]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq Procs
    /\ writers \subseteq Procs
    /\ queue \in Seq(Request)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

RequestRead(p) ==
    /\ p \notin { queue[i].proc : i \in DOMAIN queue }
    /\ queue' = Append(queue, [typ |-> "read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \notin { queue[i].proc : i \in DOMAIN queue }
    /\ queue' = Append(queue, [typ |-> "write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

BeginRead ==
    /\ queue # << >>
    /\ writers = {}
    /\ queue[1].typ = "read"
    /\ readers' = readers \cup { queue[1].proc }
    /\ queue' = Tail(queue)
    /\ UNCHANGED writers

BeginWrite ==
    /\ queue # << >>
    /\ writers = {}
    /\ readers = {}
    /\ queue[1].typ = "write"
    /\ writers' = writers \cup { queue[1].proc }
    /\ queue' = Tail(queue)
    /\ UNCHANGED readers

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Procs : RequestRead(p)
    \/ \E p \in Procs : RequestWrite(p)
    \/ BeginRead
    \/ BeginWrite
    \/ \E p \in Procs : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Procs : RequestRead(p))
    /\ WF_vars(\E p \in Procs : RequestWrite(p))
    /\ WF_vars(BeginRead)
    /\ WF_vars(BeginWrite)
    /\ WF_vars(\E p \in Procs : StopActivity(p))

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in Procs : (p \in readers) ~> (p \notin readers)
    /\ \A p \in Procs : (p \in writers) ~> (p \notin writers)

====