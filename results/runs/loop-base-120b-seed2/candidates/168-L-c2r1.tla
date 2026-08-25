---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Sequences, Naturals, TLA

CONSTANT NumActors

(* derived set of actor identifiers *)
n == 1..NumActors

VARIABLES readers, writers, q

(* a request record *)
Request == [pid : n, typ : {"read", "write"}]

(* ------------------------------------------------------------------- *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ q       = << >>

TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ q \in Seq(Request)
    /\ Cardinality(writers) <= 1

(* ------------------------------------------------------------------- *)
Pending(p, t) ==
    \E i \in 1..Len(q) : q[i].pid = p /\ q[i].typ = t

RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~Pending(p, "read")
    /\ q' = Append(q, [pid |-> p, typ |-> "read"])
    /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~Pending(p, "write")
    /\ q' = Append(q, [pid |-> p, typ |-> "write"])
    /\ UNCHANGED << readers, writers >>

ProcessQueue ==
    /\ Len(q) > 0
    /\ writers = {}
    /\ LET front == q[1] IN
         /\ IF front.typ = "read" THEN
                /\ readers' = readers \cup {front.pid}
                /\ writers' = writers
                /\ q'       = Tail(q)
            ELSE
                /\ front.typ = "write"
                /\ readers' = {}
                /\ writers' = {front.pid}
                /\ q'       = Tail(q)

Stop(p) ==
    /\ p \in n
    /\ (p \in readers \/ p \in writers)
    /\ IF p \in readers THEN
          /\ readers' = readers \ {p}
          /\ writers' = writers
       ELSE
          /\ writers' = {}
          /\ readers' = readers
    /\ UNCHANGED q

(* ------------------------------------------------------------------- *)
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

(* ------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<< readers, writers, q >> /\
    /\ \A p \in n : WF_<< readers, writers, q >>(RequestRead(p))
    /\ \A p \in n : WF_<< readers, writers, q >>(RequestWrite(p))
    /\ WF_<< readers, writers, q >>(ProcessQueue)
    /\ \A p \in n : WF_<< readers, writers, q >>(Stop(p))

Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in n : <> (p \in readers)
    /\ \A p \in n : <> (p \in writers)
    /\ \A p \in n : [] (p \in readers => <> (p \notin readers))
    /\ \A p \in n : [] (p \in writers => <> (p \notin writers))

====