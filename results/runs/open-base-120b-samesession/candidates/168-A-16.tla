---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* the .cfg substitutes n for NumActors *)
n == 1..NumActors

VARIABLES Readers, Writers, Queue

(* set of all processes *)
Proc == n

(* record that represents a request *)
Request == [pid : Proc, typ : {"read","write"}]

(* ---------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ---------------------------------------------------------------------- *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

(* ---------------------------------------------------------------------- *)
(* Helper predicates                                                       *)
(* ---------------------------------------------------------------------- *)
Queued(p, t) ==
    \E req \in Queue : /\ req.pid = p /\ req.typ = t

(* ---------------------------------------------------------------------- *)
(* Actions                                                                 *)
(* ---------------------------------------------------------------------- *)

RequestRead(p) ==
    /\ p \in Proc
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~Queued(p, "read")
    /\ Queue' = Append(Queue, [pid |-> p, typ |-> "read"])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in Proc
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~Queued(p, "write")
    /\ Queue' = Append(Queue, [pid |-> p, typ |-> "write"])
    /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ ( /\ Head(Queue).typ = "read"
         /\ Readers' = Readers \cup {Head(Queue).pid}
         /\ Writers' = Writers
         /\ Queue'   = Tail(Queue)
       )
       \/ ( /\ Head(Queue).typ = "write"
            /\ Readers = {}
            /\ Readers' = Readers
            /\ Writers' = Writers \cup {Head(Queue).pid}
            /\ Queue'   = Tail(Queue)
          )

Stop(p) ==
    /\ p \in Proc
    /\ (p \in Readers \/ p \in Writers)
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Readers' = Readers
          /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in Proc : RequestRead(p)
    \/ \E p \in Proc : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Proc : Stop(p)

(* ---------------------------------------------------------------------- *)
(* Invariants                                                              *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
    /\ Readers \subseteq Proc
    /\ Writers \subseteq Proc
    /\ Queue \in Seq(Request)
    /\ \A req \in Queue : /\ req.typ \in {"read","write"} /\ req.pid \in Proc

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(* ---------------------------------------------------------------------- *)
(* Liveness property                                                       *)
(* ---------------------------------------------------------------------- *)

Liveness ==
    /\ \A p \in Proc : <> (p \in Readers)
    /\ \A p \in Proc : <> (p \in Writers)
    /\ \A p \in Proc : [] ( (p \in Readers) => <> (p \notin Readers) )
    /\ \A p \in Proc : [] ( (p \in Writers) => <> (p \notin Writers) )

(* ---------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ---------------------------------------------------------------------- *)

Spec ==
    /\ Init
    /\ [][Next]_<<Readers, Writers, Queue>>
    /\ \A p \in Proc : WF_<<Readers, Writers, Queue>>(RequestRead(p))
    /\ \A p \in Proc : WF_<<Readers, Writers, Queue>>(RequestWrite(p))
    /\ WF_<<Readers, Writers, Queue>>(ProcessQueue)
    /\ \A p \in Proc : WF_<<Readers, Writers, Queue>>(Stop(p))

=============================================================================