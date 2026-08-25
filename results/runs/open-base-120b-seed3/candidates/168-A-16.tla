---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumActors

(*-------------------------------------------------------------------*)
(*  Derived set of actor identifiers                                   *)
(*-------------------------------------------------------------------*)
n == 1 .. NumActors
Actors == n

(*-------------------------------------------------------------------*)
(*  State variables                                                   *)
(*-------------------------------------------------------------------*)
VARIABLES readers, writers, queue

(*-------------------------------------------------------------------*)
(*  Types                                                             *)
(*-------------------------------------------------------------------*)
Req == [type : {"Read", "Write"}, pid : Actors]

(*-------------------------------------------------------------------*)
(*  Initial state                                                     *)
(*-------------------------------------------------------------------*)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

(*-------------------------------------------------------------------*)
(*  Request actions                                                   *)
(*-------------------------------------------------------------------*)
RequestRead ==
    \E p \in Actors :
        /\ p \notin readers
        /\ p \notin writers
        /\ ~(\E r \in queue : r.type = "Read" /\ r.pid = p)
        /\ readers' = readers
        /\ writers' = writers
        /\ queue'   = Append(queue, [type |-> "Read", pid |-> p])

RequestWrite ==
    \E p \in Actors :
        /\ p \notin readers
        /\ p \notin writers
        /\ ~(\E r \in queue : r.type = "Write" /\ r.pid = p)
        /\ readers' = readers
        /\ writers' = writers
        /\ queue'   = Append(queue, [type |-> "Write", pid |-> p])

(*-------------------------------------------------------------------*)
(*  Process the front of the queue                                    *)
(*-------------------------------------------------------------------*)
ProcessQueue ==
    /\ queue # << >>
    /\ writers = {}
    LET first == Head(queue) IN
        /\ IF first.type = "Read" THEN
               /\ readers' = readers \cup {first.pid}
               /\ writers' = writers
               /\ queue'   = Tail(queue)
           ELSE  \* first.type = "Write"
               /\ readers = {}
               /\ readers' = readers
               /\ writers' = writers \cup {first.pid}
               /\ queue'   = Tail(queue)
        END IF

(*-------------------------------------------------------------------*)
(*  Stop actions                                                      *)
(*-------------------------------------------------------------------*)
StopRead ==
    \E p \in readers :
        /\ readers' = readers \ {p}
        /\ writers' = writers
        /\ queue'   = queue

StopWrite ==
    \E p \in writers :
        /\ writers' = writers \ {p}
        /\ readers' = readers
        /\ queue'   = queue

(*-------------------------------------------------------------------*)
(*  Next-state relation                                                *)
(*-------------------------------------------------------------------*)
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ StopRead
    \/ StopWrite

vars == << readers, writers, queue >>

(*-------------------------------------------------------------------*)
(*  Specification                                                     *)
(*-------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(RequestRead)
        /\ WF_vars(RequestWrite)
        /\ WF_vars(ProcessQueue)
        /\ WF_vars(StopRead)
        /\ WF_vars(StopWrite)

(*-------------------------------------------------------------------*)
(*  Type correctness invariant                                        *)
(*-------------------------------------------------------------------*)
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ readers \cap writers = {}
    /\ queue \in Seq(Req)

(*-------------------------------------------------------------------*)
(*  Safety invariant                                                  *)
(*-------------------------------------------------------------------*)
Safety ==
    /\ readers \cap writers = {}
    /\ Cardinality(writers) <= 1

(*-------------------------------------------------------------------*)
(*  Liveness property (fair access for every process)                *)
(*-------------------------------------------------------------------*)
Liveness ==
    \A p \in Actors :
        ( []<>(p \in readers) ) /\ ( []<>(p \in writers) )

=============================================================================