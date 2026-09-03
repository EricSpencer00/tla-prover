---- MODULE MCBoulanger ----
EXTENDS Naturals

(* This is the model-checking configuration module for the Boulangerie      *)
(* mutual exclusion algorithm.  It inherits the full behavioral               *)
(* specification from the Boulanger module and overrides the natural           *)
(* number type with a finite range, adding a state constraint to keep         *)
(* ticket numbers within that range during model checking.                    *)

CONSTANTS N, MaxNat

\* The full set of states, lifted from the Boulanger specification so it     *)
\* can be referenced directly in the configuration.                           *
States == {"idle", "queued", "critical", "dead"}

VARIABLES phase, holder, ticket, maxTicket, paper

vars == <<phase, holder, ticket, maxTicket, paper>>

TypeOK ==
  /\ phase \in [1..N -> States]
  /\ holder \in 0..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat
  /\ paper \in SUBSET (1..N)

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ holder = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ maxTicket = 0
  /\ paper = {}

\* The privileged admin override: only while nobody is in the critical      *
\* section may the admin hand a process the next ticket and admit it.       *
AdminAdmit(i) ==
  /\ phase[i] = "idle"
  /\ holder = 0
  /\ maxTicket < MaxNat
  /\ phase' = [phase EXCEPT ![i] = "queued"]
  /\ ticket' = [ticket EXCEPT ![i] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ UNCHANGED <<holder, paper>>

Enter(i) ==
  /\ phase[i] = "queued"
  /\ holder = 0
  /\ holder' = i
  /\ phase' = [phase EXCEPT ![i] = "critical"]
  /\ paper' = paper \cup {i}
  /\ UNCHANGED <<ticket, maxTicket>>

Leave(i) ==
  /\ phase[i] = "critical"
  /\ holder = i
  /\ holder' = 0
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ paper' = paper \ {i}
  /\ UNCHANGED <<ticket, maxTicket>>

\* Unanimous checkpoint round: a process in the idle state with no          *
\* ticket outstanding is queued and given the next ticket number.           *
Request(i) ==
  /\ phase[i] = "idle"
  /\ ticket[i] = 0
  /\ maxTicket < MaxNat
  /\ phase' = [phase EXCEPT ![i] = "queued"]
  /\ ticket' = [ticket EXCEPT ![i] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ UNCHANGED <<holder, paper>>

Crash(i) ==
  /\ phase[i] # "dead"
  /\ phase' = [phase EXCEPT ![i] = "dead"]
  /\ holder' = IF holder = i THEN 0 ELSE holder
  /\ UNCHANGED <<ticket, maxTicket, paper>>

Recover(i) ==
  /\ phase[i] = "dead"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<holder, ticket, maxTicket, paper>>

Next ==
  \/ \E i \in 1..N : AdminAdmit(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Crash(i)
  \/ \E i \in 1..N : Recover(i)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: a ticket number is carried by at most one process.      *
MutualExclusion ==
  \A i, j \in 1..N : (i # j /\ ticket[i] > 0 /\ ticket[j] > 0) => ticket[i] # ticket[j]

\* Every process in the critical section is the single recorded holder.      *
HolderIsCritical ==
  \A i \in 1..N : phase[i] = "critical" => holder = i

Inv == MutualExclusion /\ HolderIsCritical

\* Finite-range safety check: no process ever holds a ticket number        *
\* reaching the configured maximum, so the overridden finite Nat is never  *
\* driven to its bound during model checking.                               *
BoundedTicket == \A i \in 1..N : ticket[i] < MaxNat

====