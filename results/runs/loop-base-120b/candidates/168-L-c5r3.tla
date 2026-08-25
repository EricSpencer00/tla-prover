---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumActors
VARIABLES Readers, Writers, Queue

(* --------------------------------------------------------------------- *)
(* Helper definitions                                                   *)
(* --------------------------------------------------------------------- *)

(* Finite set of actor identifiers *)
Actors == 1 .. NumActors

(* Helper to create a request record *)
Req(p, t) == [proc |-> p, type |-> t]

(* Is process p already waiting in the queue? *)
InQueue(p) ==
    \E i \in 1 .. Len(Queue) : Queue[i].proc = p

(* --------------------------------------------------------------------- *)
(* Actions                                                             *)
(* --------------------------------------------------------------------- *)

(* 1. Request to read *)
RequestRead(p) ==
    /\ p \in Actors
    /\ ~InQueue(p)
    /\ Queue' = Append(Queue, Req(p, "read"))
    /\ UNCHANGED <<Readers, Writers>>

RequestReadAction == \E p \in Actors : RequestRead(p)

(* 2. Request to write *)
RequestWrite(p) ==
    /\ p \in Actors
    /\ ~InQueue(p)
    /\ Queue' = Append(Queue, Req(p, "write"))
    /\ UNCHANGED <<Readers, Writers>>

RequestWriteAction == \E p \in Actors : RequestWrite(p)

(* 3. Begin reading or writing (process the queue) *)
ProcessQueue ==
    /\ Len(Queue) > 0
    /\ LET front == Queue[1] IN
         /\ Writers = {}
         /\ ( /\ front.type = "read"
                /\ Readers' = Readers \cup {front.proc}
                /\ Writers' = Writers
                /\ Queue'   = Tail(Queue)
            \/ /\ front.type = "write"
                /\ Readers = {}
                /\ Readers' = Readers
                /\ Writers' = Writers \cup {front.proc}
                /\ Queue'   = Tail(Queue) )

(* 4. Stop activity *)
Stop(p) ==
    /\ p \in Actors
    /\ ( /\ p \in Readers
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       \/ /\ p \in Writers
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers )
    /\ UNCHANGED Queue

StopAction == \E p \in Actors : Stop(p)

(* --------------------------------------------------------------------- *)
(* Next-state relation                                                  *)
(* --------------------------------------------------------------------- *)
Next == RequestReadAction \/ RequestWriteAction \/ ProcessQueue \/ StopAction

(* --------------------------------------------------------------------- *)
(* Initial state                                                        *)
(* --------------------------------------------------------------------- *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

(* --------------------------------------------------------------------- *)
(* Specification (with weak fairness on all actions)                    *)
(* --------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>
        /\ WF_<<Readers, Writers, Queue>>(RequestReadAction)
        /\ WF_<<Readers, Writers, Queue>>(RequestWriteAction)
        /\ WF_<<Readers, Writers, Queue>>(ProcessQueue)
        /\ WF_<<Readers, Writers, Queue>>(StopAction)

(* --------------------------------------------------------------------- *)
(* Type invariant                                                       *)
(* --------------------------------------------------------------------- *)
TypeOK ==
    /\ Readers \subseteq Actors
    /\ Writers \subseteq Actors
    /\ \A i \in 1 .. Len(Queue) :
          /\ Queue[i].proc \in Actors
          /\ Queue[i].type \in {"read", "write"}

(* --------------------------------------------------------------------- *)
(* Safety invariant                                                     *)
(* --------------------------------------------------------------------- *)
Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

(* --------------------------------------------------------------------- *)
(* Liveness property                                                    *)
(* --------------------------------------------------------------------- *)
Liveness ==
    \A p \in Actors :
        (<> (p \in Readers) /\ <> (p \in Writers))
        /\ [] (p \in Readers => <> (p \notin Readers))
        /\ [] (p \in Writers => <> (p \notin Writers))

====