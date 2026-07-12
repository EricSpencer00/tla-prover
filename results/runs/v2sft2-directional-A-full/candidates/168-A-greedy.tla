---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

VARIABLES Readers, Writers, Queue

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ Readers \subseteq 1..NumActors
    /\ Writers \subseteq 1..NumActors
    /\ Queue \in Seq({ "Read" \* 1..NumActors,
                       "Write" \* 1..NumActors })
    /\ \A r \in Queue : r \in {"Read" \* 1..NumActors, "Write" \* 1..NumActors}

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = <<>>

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* Request to read: a process not already waiting to read joins the queue *)
RequestRead(p) ==
    /\ p \in 1..NumActors
    /\ ~(\E q \in Queue : q = ("Read" \* p))
    /\ Queue' = Append(Queue, ("Read" \* p))
    /\ UNCHANGED <<Readers, Writers>>

(* Request to write: a process not already waiting to write joins the queue *)
RequestWrite(p) ==
    /\ p \in 1..NumActors
    /\ ~(\E q \in Queue : q = ("Write" \* p))
    /\ Queue' = Append(Queue, ("Write" \* p))
    /\ UNCHANGED <<Readers, Writers>>

(* Begin reading or writing: process the front of the queue if possible *)
ProcessQueue ==
    /\ Queue # <<>>
    /\ LET front == Head(Queue) IN
       \E p \in 1..NumActors :
          /\ front = ("Read" \* p)
          /\ Writers = {}
          /\ Queue' = Tail(Queue)
          /\ Readers' = Readers \cup {p}
          /\ UNCHANGED Writers
          \/ front = ("Write" \* p)
          /\ Readers = {}
          /\ Queue' = Tail(Queue)
          /\ Writers' = Writers \cup {p}
          /\ UNCHANGED Readers

(* Stop activity: a reader or writer may voluntarily stop *)
Stop(p) ==
    /\ p \in 1..NumActors
    /\ (p \in Readers \/ p \in Writers)
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ UNCHANGED <<Writers, Queue>>
       ELSE
          /\ Writers' = Writers \ {p}
          /\ UNCHANGED <<Readers, Queue>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in 1..NumActors : RequestRead(p)
    \/ \E p \in 1..NumActors : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in 1..NumActors : Stop(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

(* ----------------------------------------------------------------------
   Safety invariant: no reader and writer are active together, and at most one writer
   ---------------------------------------------------------------------- *)
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(* ----------------------------------------------------------------------
   Liveness property: every process eventually gets to read and eventually gets to write
   ---------------------------------------------------------------------- *)
Liveness ==
    \A p \in 1..NumActors :
        (WF_vars(Readers, p) /\ WF_vars(Writers, p))

(* ----------------------------------------------------------------------
   Helper for weak fairness of a variable being set to a value
   ---------------------------------------------------------------------- *)
WF_vars(v, p) == WF_vars(v, p)

====