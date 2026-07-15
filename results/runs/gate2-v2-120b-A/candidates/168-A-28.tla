---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS NumActors

(* ---------------------------------------------------------------------- *)
(* Derived constants *)
Readers == 1 .. NumActors
Writers == Readers   \* same identifier set, used for readability
Processes == Readers

ProcType == {"r", "w"}

(* ---------------------------------------------------------------------- *)
(* State variables *)
VARIABLES ReadersSet, WritersSet, Queue

vars == << ReadersSet, WritersSet, Queue >>

(* ---------------------------------------------------------------------- *)
(* Types *)
TypeSet == SUBSET Processes
TypeQueue == Seq( [type : ProcType, proc : Processes] )
TypeOK == /\ ReadersSet \in TypeSet
         /\ WritersSet \in TypeSet
         /\ Queue \in TypeQueue

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ ReadersSet = {}
    /\ WritersSet = {}
    /\ Queue = <<>>

(* ---------------------------------------------------------------------- *)
(* Helper to check if a process is already waiting in the queue *)
Waiting(p) == \E i \in 1..Len(Queue) : Queue[i].proc = p

(* ---------------------------------------------------------------------- *)
(* Actions *)

RequestRead(p) ==
    /\ p \in Processes
    /\ ~Waiting(p)
    /\ Queue' = Queue \o << [type |-> "r", proc |-> p] >>
    /\ UNCHANGED << ReadersSet, WritersSet >>

RequestWrite(p) ==
    /\ p \in Processes
    /\ ~Waiting(p)
    /\ Queue' = Queue \o << [type |-> "w", proc |-> p] >>
    /\ UNCHANGED << ReadersSet, WritersSet >>

BeginProcessing ==
    /\ Len(Queue) > 0
    /\ WritersSet = {}          \* no writer currently active
    /\ LET front == Queue[1] IN
       IF front.type = "r" THEN
          /\ ReadersSet' = ReadersSet \cup {front.proc}
          /\ WritersSet' = WritersSet
          /\ Queue' = Tail(Queue)
       ELSE   \* front.type = "w"
          /\ ReadersSet = {}    \* no readers active
          /\ WritersSet' = {front.proc}
          /\ Queue' = Tail(Queue)

StopRead(p) ==
    /\ p \in ReadersSet
    /\ ReadersSet' = ReadersSet \ {p}
    /\ UNCHANGED << WritersSet, Queue >>

StopWrite(p) ==
    /\ p \in WritersSet
    /\ WritersSet' = {}
    /\ UNCHANGED << ReadersSet, Queue >>

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ \E p \in Processes : RequestRead(p)
    \/ \E p \in Processes : RequestWrite(p)
    \/ BeginProcessing
    \/ \E p \in Processes : StopRead(p)
    \/ \E p \in Processes : StopWrite(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Safety invariant (the required "Safety") *)
Safety ==
    /\ (ReadersSet = {} \/ WritersSet = {})
    /\ Cardinality(WritersSet) <= 1

(* ---------------------------------------------------------------------- *)
(* Liveness properties (the required "Liveness") *)
(* 1. Every process eventually reads *)
EventuallyRead(p) ==
    <> (p \in ReadersSet)

(* 2. Every process eventually writes *)
EventuallyWrite(p) ==
    <> (p \in WritersSet)

(* 3. Every active reader eventually stops *)
ReaderStops(p) ==
    [] (p \in ReadersSet => <> (p \notin ReadersSet))

(* 4. Every active writer eventually stops *)
WriterStops(p) ==
    [] (p \in WritersSet => <> (p \notin WritersSet))

(* Combine into a single property as required by the .cfg *)
Liveness ==
    /\ \A p \in Processes : EventuallyRead(p)
    /\ \A p \in Processes : EventuallyWrite(p)
    /\ \A p \in Processes : ReaderStops(p)
    /\ \A p \in Processes : WriterStops(p)

====