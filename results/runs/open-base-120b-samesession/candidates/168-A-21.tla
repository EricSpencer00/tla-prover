---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(*--------------------------------------------------------------------
  Derived constant used by the .cfg file (substituted for NumActors)
--------------------------------------------------------------------*)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
IsRequest(r) == /\ r \in [proc : n, type : {"read", "write"}]

SeqToSet(s) == { e \in DOMAIN s : s[e] }

IsWaiting(p, t) == 
    \E q \in SeqToSet(Queue) : /\ q.proc = p
                               /\ q.type = t

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
RequestRead(p) ==
    /\ p \in n
    /\ ~IsWaiting(p, "read")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ ~IsWaiting(p, "write")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED <<Readers, Writers>>

BeginRead ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "read"
    /\ Writers = {}
    /\ Readers' = Readers \cup {Head(Queue).proc}
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

BeginWrite ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "write"
    /\ Writers = {}
    /\ Readers = {}
    /\ Writers' = Writers \cup {Head(Queue).proc}
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

StopReader(p) ==
    /\ p \in Readers
    /\ Readers' = Readers \ {p}
    /\ Writers' = Writers
    /\ UNCHANGED <<Queue>>

StopWriter(p) ==
    /\ p \in Writers
    /\ Writers' = Writers \ {p}
    /\ Readers' = Readers
    /\ UNCHANGED <<Queue>>

Stop(p) == StopReader(p) \/ StopWriter(p)

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ BeginRead
    \/ BeginWrite
    \/ \E p \in n : Stop(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Cardinality(Writers) <= 1
    /\ Readers \cap Writers = {}
    /\ \A r \in SeqToSet(Queue) : IsRequest(r)

Safety ==
    /\ (Readers = {} \/ Writers = {})
    /\ Cardinality(Writers) <= 1
    /\ Readers \cap Writers = {}

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)
Liveness ==
    /\ \A p \in n : <> (p \in Readers)
    /\ \A p \in n : <> (p \in Writers)
    /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))
    /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))

====