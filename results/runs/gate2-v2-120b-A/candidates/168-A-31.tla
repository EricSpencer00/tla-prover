---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS NumActors

(* --- Derived sets --- *)
ProcSet == 1..NumActors

(* --- Types for queue entries --- *)
ReadReq == 1
WriteReq == 2

Request == [type : {ReadReq, WriteReq}, proc : ProcSet]

(* --- State variables --- *)
VARIABLES r, w, q

(* --- Helper definitions --- *)
Readers == r
Writers == w
Queue   == q

(* --- Initial state --- *)
Init ==
    /\ r = {}
    /\ w = {}
    /\ q = << >>

(* --- Actions --- *)

(* Request to read *)
ReqRead(p) ==
    /\ p \in ProcSet
    /\ ~(\E i \in 1..Len(q): q[i].proc = p /\ q[i].type = ReadReq)  \* not already waiting to read
    /\ q' = Append(q, [type |-> ReadReq, proc |-> p])
    /\ UNCHANGED << r, w >>

(* Request to write *)
ReqWrite(p) ==
    /\ p \in ProcSet
    /\ ~(\E i \in 1..Len(q): q[i].proc = p /\ q[i].type = WriteReq) \* not already waiting to write
    /\ q' = Append(q, [type |-> WriteReq, proc |-> p])
    /\ UNCHANGED << r, w >>

(* Begin reading or writing from the front of the queue *)
ProcessQueue ==
    /\ Len(q) > 0
    /\ q[1].type = ReadReq
    /\ w = {}                         \* no writer active
    /\ r' = Readers \cup { q[1].proc }
    /\ q' = Tail(q)
    /\ UNCHANGED w
  \/ 
    /\ Len(q) > 0
    /\ q[1].type = WriteReq
    /\ r = {}                         \* no readers active
    /\ w' = Writers \cup { q[1].proc }
    /\ q' = Tail(q)
    /\ UNCHANGED r

(* Stop activity for a reader *)
StopRead(p) ==
    /\ p \in Readers
    /\ r' = Readers \ {p}
    /\ UNCHANGED << w, q >>

(* Stop activity for a writer *)
StopWrite(p) ==
    /\ p \in Writers
    /\ w' = Writers \ {p}
    /\ UNCHANGED << r, q >>

(* --- Next-state relation --- *)
Next ==
    \/ \E p \in ProcSet : ReqRead(p)
    \/ \E p \in ProcSet : ReqWrite(p)
    \/ ProcessQueue
    \/ \E p \in ProcSet : StopRead(p)
    \/ \E p \in ProcSet : StopWrite(p)

(* --- Specification --- *)
Spec == Init /\ [][Next]_<<r, w, q>>

(* --- Type invariant --- *)
TypeOK ==
    /\ r \subseteq ProcSet
    /\ w \subseteq ProcSet
    /\ \A i \in 1..Len(q) : q[i] \in Request

(* --- Safety invariant (readers and writers never active together,
     and at most one writer) --- *)
Safety ==
    /\ (w = {} \/ r = {})
    /\ Cardinality(w) <= 1

(* --- Liveness property: every process eventually reads and writes --- *)
Liveness ==
    /\ \A p \in ProcSet : <> (p \in Readers)   \* eventual reading
    /\ \A p \in ProcSet : <> (p \in Writers)   \* eventual writing

====