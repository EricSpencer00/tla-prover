---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences

CONSTANTS NumActors

VARIABLES activeReaders, activeWriters, pending

Vars == <<activeReaders, activeWriters, pending>>

TypeOK ==
    /\ activeReaders \subseteq NumActors
    /\ activeWriters \subseteq NumActors
    /\ pending \in Seq([proc: NumActors, kind: {"read", "write"}])

Init ==
    /\ activeReaders = {}
    /\ activeWriters = {}
    /\ pending = <<>>

RequestRead(p) ==
    /\ [proc |-> p, kind |-> "read"] \notin pending
    /\ pending' = Append(pending, [proc |-> p, kind |-> "read"])
    /\ UNCHANGED <<activeReaders, activeWriters>>

RequestWrite(p) ==
    /\ [proc |-> p, kind |-> "write"] \notin pending
    /\ pending' = Append(pending, [proc |-> p, kind |-> "write"])
    /\ UNCHANGED <<activeReaders, activeWriters>>

ProcessQueue ==
    /\ Len(pending) > 0
    /\ activeWriters = {}
    /\ LET head == Head(pending) IN
         /\ IF head.kind = "read" THEN activeReaders' = activeReaders \cup {head.proc}
            ELSE IF activeReaders = {} /\ activeWriters' = activeWriters \cup {head.proc}
            ELSE UNCHANGED activeWriters
         /\ pending' = Tail(pending)
    /\ UNCHANGED activeWriters

StopActivity(p) ==
    /\ (p \in activeReaders \/ p \in activeWriters)
    /\ activeReaders' = activeReaders \ {p}
    /\ activeWriters' = activeWriters \ {p}
    /\ UNCHANGED pending

Next ==
    \/ ProcessQueue
    \/ \E p \in NumActors: RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)

Spec == Init /\ [][Next]_Vars
    /\ WF_Vars(ProcessQueue)
    /\ \A p \in NumActors: WF_Vars(RequestRead(p)) /\ WF_Vars(RequestWrite(p)) /\ WF_Vars(StopActivity(p))

Safety ==
    /\ (activeWriters # {}) => (activeReaders = {})
    /\ (activeReaders # {}) => (activeWriters = {})

Liveness ==
    /\ (\A p \in NumActors: <> (p \in activeReaders))
    /\ (\A p \in NumActors: <> (p \in activeWriters))
    /\ (\A p \in NumActors: (p \in activeReaders) ~> (p \notin activeReaders))
    /\ (\A p \in NumActors: (p \in activeWriters) ~> (p \notin activeWriters))

n == 2
====