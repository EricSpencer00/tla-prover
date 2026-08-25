---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(* Set of actor identifiers *)
n == 1..NumActors

VARIABLES readers, writers, queue

(* --------------------------------------------------------------
   Type invariant
   -------------------------------------------------------------- *)
TypeOK ==
    /\ readers \in SUBSET n
    /\ writers \in SUBSET n
    /\ queue \in Seq([proc : n, type : {"read","write"}])

(* --------------------------------------------------------------
   Initial state
   -------------------------------------------------------------- *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

(* --------------------------------------------------------------
   Actions
   -------------------------------------------------------------- *)

(* A process requests to read *)
RequestRead ==
    \E p \in n :
        /\ p \notin readers
        /\ p \notin writers
        /\ p \notin { q.proc : q \in queue }
        /\ queue' = Append(queue, [proc |-> p, type |-> "read"])
        /\ UNCHANGED <<readers, writers>>

(* A process requests to write *)
RequestWrite ==
    \E p \in n :
        /\ p \notin readers
        /\ p \notin writers
        /\ p \notin { q.proc : q \in queue }
        /\ queue' = Append(queue, [proc |-> p, type |-> "write"])
        /\ UNCHANGED <<readers, writers>>

(* The first request in the queue is processed *)
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    LET first == Head(queue) IN
        \/ /\ first.type = "read"
            /\ readers' = readers \cup {first.proc}
            /\ writers' = writers
            /\ queue'   = Tail(queue)
        \/ /\ first.type = "write"
            /\ readers = {}
            /\ writers' = {first.proc}
            /\ readers' = readers
            /\ queue'   = Tail(queue)
    /\ UNCHANGED <<>>

(* A reader or writer stops its activity *)
StopActivity ==
    \E p \in n :
        \/ /\ p \in readers
            /\ readers' = readers \ {p}
            /\ writers' = writers
            /\ UNCHANGED queue
        \/ /\ p \in writers
            /\ writers' = {}
            /\ readers' = readers
            /\ UNCHANGED queue

Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ StopActivity

vars == <<readers, writers, queue>>

(* --------------------------------------------------------------
   Specification
   -------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_vars
        /\ WF_{vars}(RequestRead)
        /\ WF_{vars}(RequestWrite)
        /\ WF_{vars}(ProcessQueue)
        /\ WF_{vars}(StopActivity)

(* --------------------------------------------------------------
   Safety properties
   -------------------------------------------------------------- *)
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

(* --------------------------------------------------------------
   Liveness properties
   -------------------------------------------------------------- *)
Liveness ==
    /\ \A p \in n : <> (p \in readers)          (* every process eventually reads *)
    /\ \A p \in n : <> (p \in writers)          (* every process eventually writes *)
    /\ \A p \in n : [] (p \in readers => <> (p \notin readers))
    /\ \A p \in n : [] (p \in writers => <> (p \notin writers))

====