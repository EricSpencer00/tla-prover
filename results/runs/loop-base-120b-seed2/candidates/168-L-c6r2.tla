---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue

(* ------------------------------------------------------------------------ *)
(* Types and invariants                                                    *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ readers \cap writers = {}
    /\ queue \in Seq([proc : n, op : {"Read", "Write"}])

Safety ==
    /\ \A p \in writers : Cardinality(writers) = 1
    /\ readers \cap writers = {}

(* ------------------------------------------------------------------------ *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

(* ------------------------------------------------------------------------ *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------ *)

NotInQueue(p) ==
    ~(\E i \in 1..Len(queue) : queue[i].proc = p)

Front == Head(queue)

(* ------------------------------------------------------------------------ *)
(* Actions                                                                  *)
(* ------------------------------------------------------------------------ *)

ReqRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ NotInQueue(p)
    /\ queue' = Append(queue, [proc |-> p, op |-> "Read"])
    /\ UNCHANGED <<readers, writers>>

ReqWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ NotInQueue(p)
    /\ queue' = Append(queue, [proc |-> p, op |-> "Write"])
    /\ UNCHANGED <<readers, writers>>

BeginRead ==
    /\ queue # <<>>
    /\ Front.op = "Read"
    /\ writers = {}
    /\ readers' = readers \cup {Front.proc}
    /\ writers' = writers
    /\ queue'   = Tail(queue)
    /\ UNCHANGED <<>>

BeginWrite ==
    /\ queue # <<>>
    /\ Front.op = "Write"
    /\ writers = {}
    /\ readers = {}
    /\ writers' = {Front.proc}
    /\ readers' = readers
    /\ queue'   = Tail(queue)
    /\ UNCHANGED <<>>

StopRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

StopWrite(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ UNCHANGED <<readers, queue>>

(* ------------------------------------------------------------------------ *)
(* Next step                                                               *)
(* ------------------------------------------------------------------------ *)

Next ==
    \/ \E p \in n : ReqRead(p)
    \/ \E p \in n : ReqWrite(p)
    \/ BeginRead
    \/ BeginWrite
    \/ \E p \in readers : StopRead(p)
    \/ \E p \in writers : StopWrite(p)

(* ------------------------------------------------------------------------ *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------ *)

Spec ==
    Init /\ [][Next]_<<readers, writers, queue>> /\ WF_<<readers, writers, queue>>(Next)

(* ------------------------------------------------------------------------ *)
(* Liveness property (fairness for each process)                           *)
(* ------------------------------------------------------------------------ *)

Liveness ==
    \A p \in n : <> (p \in readers) /\ <> (p \in writers)

(* ------------------------------------------------------------------------ *)
(* Theorem declarations (optional, for model checking)                     *)
(* ------------------------------------------------------------------------ *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness

====