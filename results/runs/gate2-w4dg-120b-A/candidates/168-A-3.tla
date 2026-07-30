---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Processes == 1 .. NumActors
Modes == {"read", "write"}
NoReq == [who |-> 0, mode |-> "none"]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq Processes
    /\ writers \subseteq Processes
    /\ queue \in Seq([who : Processes, mode : Modes])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

ArriveRead(p) ==
    /\ \A i \in DOMAIN queue : queue[i].who # p
    /\ queue' = Append(queue, [who |-> p, mode |-> "read"])
    /\ UNCHANGED <<readers, writers>>

ArriveWrite(p) ==
    /\ \A i \in DOMAIN queue : queue[i].who # p
    /\ queue' = Append(queue, [who |-> p, mode |-> "write"])
    /\ UNCHANGED <<readers, writers>>

BeginService ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET h == Head(queue) IN
         /\ queue' = Tail(queue)
         /\ IF h.mode = "read" THEN readers' = readers \cup {h.who} ELSE
              /\ h.mode = "write"
              /\ readers = {}
              /\ writers' = {h.who}
    /\ UNCHANGED writers

ArriveReadWF == ArriveRead
ArriveWriteWF == ArriveWrite
BeginServiceWF == BeginService

StopActivity(p) ==
    \/ /\ p \in readers
       /\ readers' = readers \ {p}
       /\ UNCHANGED writers
    \/ /\ p \in writers
       /\ writers' = writers \ {p}
       /\ UNCHANGED readers
    /\ UNCHANGED queue

StopActivityWF == StopActivity

Next ==
    \/ \E p \in Processes : ArriveRead(p)
    \/ \E p \in Processes : ArriveWrite(p)
    \/ BeginService
    \/ \E p \in Processes : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ArriveReadWF)
    /\ WF_vars(ArriveWriteWF)
    /\ WF_vars(BeginServiceWF)
    /\ WF_vars(StopActivityWF)

Safety ==
    /\ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in Processes : (p \in readers) ~> (p \notin readers)
    /\ \A p \in Processes : (p \in writers) ~> (p \notin writers)

====