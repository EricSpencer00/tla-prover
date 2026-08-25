---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS NumActors

(* the set of actor identifiers *)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

(* ------------------------------------------------------------------- *)
(* Type invariant                                                      *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq([type : {"read","write"}, proc : n])

(* ------------------------------------------------------------------- *)
(* Initial state                                                       *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

(* ------------------------------------------------------------------- *)
(* Actions                                                             *)
(* ------------------------------------------------------------------- *)

RequestRead(p) ==
    /\ p \in n
    /\ p \notin { Queue[i].proc : i \in 1 .. Len(Queue) }
    /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin { Queue[i].proc : i \in 1 .. Len(Queue) }
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

StartRead ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "read"
    /\ Writers = {}
    /\ Readers' = Readers \cup { Head(Queue).proc }
    /\ Queue'   = Tail(Queue)
    /\ UNCHANGED Writers

StartWrite ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "write"
    /\ Writers = {}
    /\ Readers = {}
    /\ Writers' = Writers \cup { Head(Queue).proc }
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)
    /\ UNCHANGED Readers

Stop(p) ==
    /\ p \in n
    /\ (p \in Readers) \/ (p \in Writers)
    /\ IF p \in Readers
          THEN /\ Readers' = Readers \ {p}
               /\ Writers' = Writers
          ELSE /\ Readers' = Readers
               /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ StartRead
    \/ StartWrite
    \/ \E p \in n : Stop(p)

(* ------------------------------------------------------------------- *)
(* Specification                                                       *)
(* ------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>> /\ WF_vars(Next)

(* ------------------------------------------------------------------- *)
(* Safety properties                                                   *)
(* ------------------------------------------------------------------- *)
Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

(* ------------------------------------------------------------------- *)
(* Liveness property                                                   *)
(* ------------------------------------------------------------------- *)
Liveness ==
    \A p \in n : <> (p \in Readers) /\ <> (p \in Writers)

====