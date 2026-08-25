---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(* Set of actor identifiers *)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

(*-----------------------------------------------------------------
   Type invariant
-----------------------------------------------------------------*)
TypeOK ==
  /\ Readers \subseteq n
  /\ Writers \subseteq n
  /\ Disjoint(Readers, Writers)
  /\ Queue \in Seq([proc : n, kind : {"read", "write"}])

(*-----------------------------------------------------------------
   Initial state
-----------------------------------------------------------------*)
Init ==
  /\ Readers = {}
  /\ Writers = {}
  /\ Queue   = <<>>

(*-----------------------------------------------------------------
   Helper: is there a pending request of a given kind for a process?
-----------------------------------------------------------------*)
Pending(p, k) ==
  \E i \in DOMAIN Queue :
    /\ Queue[i].proc = p
    /\ Queue[i].kind = k

(*-----------------------------------------------------------------
   Actions
-----------------------------------------------------------------*)
RequestRead(p) ==
  /\ p \in n
  /\ p \notin Readers
  /\ p \notin Writers
  /\ ~ Pending(p, "read")
  /\ Queue' = Append(Queue, [proc |-> p, kind |-> "read"])
  /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
  /\ p \in n
  /\ p \notin Readers
  /\ p \notin Writers
  /\ ~ Pending(p, "write")
  /\ Queue' = Append(Queue, [proc |-> p, kind |-> "write"])
  /\ UNCHANGED <<Readers, Writers>>

Begin ==
  /\ Len(Queue) > 0
  /\ LET front == Queue[1] IN
        ( /\ front.kind = "read"
           /\ Writers = {}
           /\ Readers' = Readers \cup {front.proc}
           /\ Queue'   = Tail(Queue)
           /\ UNCHANGED Writers )
        \/ ( /\ front.kind = "write"
            /\ Writers = {}
            /\ Readers = {}
            /\ Writers' = {front.proc}
            /\ Queue'   = Tail(Queue)
            /\ UNCHANGED Readers )

Stop(p) ==
  /\ p \in n
  /\ (p \in Readers \/ p \in Writers)
  /\ IF p \in Readers
        THEN /\ Readers' = Readers \ {p}
             /\ UNCHANGED <<Writers, Queue>>
        ELSE /\ Writers' = Writers \ {p}
             /\ UNCHANGED <<Readers, Queue>>

Next ==
  \/ \E p \in n : RequestRead(p)
  \/ \E p \in n : RequestWrite(p)
  \/ Begin
  \/ \E p \in n : Stop(p)

vars == <<Readers, Writers, Queue>>

(*-----------------------------------------------------------------
   Specification with weak fairness on all actions
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_vars
        /\ WF_vars(RequestRead)
        /\ WF_vars(RequestWrite)
        /\ WF_vars(Begin)
        /\ WF_vars(Stop)

(*-----------------------------------------------------------------
   Safety properties
-----------------------------------------------------------------*)
Safety ==
  /\ (Writers = {} \/ Readers = {})
  /\ Cardinality(Writers) <= 1

(*-----------------------------------------------------------------
   Liveness properties
-----------------------------------------------------------------*)
Liveness ==
  /\ \A p \in n :
        (<> (p \in Readers) /\ <> (p \in Writers))
        /\ [] (p \in Readers => <> (p \notin Readers))
        /\ [] (p \in Writers => <> (p \notin Writers))

====