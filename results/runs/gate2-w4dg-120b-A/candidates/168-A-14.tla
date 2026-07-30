---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Processes == 1 .. NumActors

VARIABLES readerSet, writerSet, queue
vars == <<readerSet, writerSet, queue>>

QueueCell == [actor : Processes, mode : {"read", "write"}]

TypeOK ==
    /\ readerSet \subseteq Processes
    /\ writerSet \subseteq Processes
    /\ queue \in Seq(QueueCell)

Init ==
    /\ readerSet = {}
    /\ writerSet = {}
    /\ queue = << >>

EnqueueRead(p) ==
    /\ p \notin (IF queue = << >> THEN {} ELSE {queue[1].actor} :> {queue[1].actor})
    /\ queue' = Append(queue, [actor |-> p, mode |-> "read"])
    /\ UNCHANGED <<readerSet, writerSet>>

EnqueueWrite(p) ==
    /\ p \notin (IF queue = << >> THEN {} ELSE {queue[1].actor} :> {queue[1].actor})
    /\ queue' = Append(queue, [actor |-> p, mode |-> "write"])
    /\ UNCHANGED <<readerSet, writerSet>>

ProcessQueue ==
    /\ queue # << >>
    /\ Cardinality(writerSet) = 0
    /\ \/ /\ queue[1].mode = "read"
          /\ readerSet' = readerSet \cup {queue[1].actor}
          /\ queue' = Tail(queue)
          /\ UNCHANGED writerSet
       \/ /\ queue[1].mode = "write"
          /\ readerSet = {}
          /\ writerSet' = writerSet \cup {queue[1].actor}
          /\ queue' = Tail(queue)
          /\ UNCHANGED readerSet

StopActivity(p) ==
    /\ \/ p \in readerSet /\ readerSet' = readerSet \ {p}
       \/ p \in writerSet /\ writerSet' = writerSet \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Processes : EnqueueRead(p)
    \/ \E p \in Processes : EnqueueWrite(p)
    \/ ProcessQueue
    \/ \E p \in Processes : StopActivity(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in Processes : EnqueueRead(p))
        /\ WF_vars(\E p \in Processes : EnqueueWrite(p))
        /\ WF_vars(ProcessQueue)
        /\ \A p \in Processes : WF_vars(StopActivity(p))

Safety ==
    /\ (readerSet # {} => writerSet = {})
    /\ (writerSet # {} => readerSet = {})
    /\ \A a, b \in writerSet : a = b

Liveness ==
    /\ \A p \in Processes : [][~(p \in readerSet)]_vars
    /\ \A p \in Processes : [][~(p \in writerSet)]_vars
    /\ \A p \in Processes : <>(p \in readerSet)
    /\ \A p \in Processes : <>(p \in writerSet)

====