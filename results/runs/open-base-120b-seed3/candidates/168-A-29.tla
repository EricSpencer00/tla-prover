---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\*  Set of actor identifiers (will be overridden by the .cfg file)
\* ----------------------------------------------------------------------
n == 1 .. NumActors

VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
Request == [type : {"read", "write"}, proc : n]

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
IsInQueue(p) == \E i \in DOMAIN queue : queue[i].proc = p
Front == queue[1]

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
\*  Request to read
ReqRead(p) ==
    /\ p \in n
    /\ ~IsInQueue(p)
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ readers' = readers
    /\ writers' = writers

\*  Request to write
ReqWrite(p) ==
    /\ p \in n
    /\ ~IsInQueue(p)
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ readers' = readers
    /\ writers' = writers

\*  Process the queue (grant access)
Proc ==
    /\ queue # <<>>
    /\ writers = {}                                   \* no writer currently
    /\ LET ft == Front IN
       /\ ft.proc \notin readers \/ writers            \* not already active
       /\ CASE ft.type = "read" ->
              /\ readers' = readers \cup {ft.proc}
              /\ writers' = writers
          [] ft.type = "write" ->
              /\ readers = {}                           \* no readers
              /\ writers' = {ft.proc}
              /\ readers' = readers
       /\ queue' = Tail(queue)

\*  Stop activity
Stop(p) ==
    \/ /\ p \in readers
       /\ readers' = readers \ {p}
       /\ writers' = writers
       /\ queue'   = queue
    \/ /\ p \in writers
       /\ writers' = writers \ {p}
       /\ readers' = readers
       /\ queue'   = queue

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in n : ReqRead(p)
    \/ \E p \in n : ReqWrite(p)
    \/ Proc
    \/ \E p \in n : Stop(p)

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<readers, writers, queue>> /\
    WF_<<readers, writers, queue>>( \E p \in n : ReqRead(p) ) /\
    WF_<<readers, writers, queue>>( \E p \in n : ReqWrite(p) ) /\
    WF_<<readers, writers, queue>>( Proc ) /\
    WF_<<readers, writers, queue>>( \E p \in n : Stop(p) )

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ readers \cap writers = {}
    /\ Cardinality(writers) <= 1
    /\ /\ queue \in Seq(Request)
       /\ \A i \in DOMAIN queue :
            /\ queue[i].type \in {"read", "write"}
            /\ queue[i].proc \in n

Safety ==
    /\ (writers = {} \/ readers = {})      \* no simultaneous readers & writers
    /\ Cardinality(writers) <= 1           \* at most one writer

\* ----------------------------------------------------------------------
\*  Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        (<> (p \in readers) /\ <> (p \in writers))      \* each process eventually reads and writes
        /\ [] (p \in readers => <> (p \notin readers)) \* readers eventually stop
        /\ [] (p \in writers => <> (p \notin writers)) \* writers eventually stop

====