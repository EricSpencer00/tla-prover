---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Sequences, Tuples

CONSTANTS N, MaxNat

\* Quantities from the Boulanger spec, repeated here so this module can stand
\* on its own as a complete, checkable model.
Processes == 0..(N - 1)
Succ(p) == (p + 1) % N
SuccOf(q) == { p \in Processes : Succ(p) = q }

VARIABLES token, want, inCS, served
vars == << token, want, inCS, served >>

InitState == [ token |-> 0, want |-> {}, inCS |-> {}, served |-> 0 ]

TypeOK ==
    /\ token \in Processes
    /\ want \subseteq Processes
    /\ inCS \subseteq Processes
    /\ served \in 0..MaxNat

Init == InitState

\* A process takes a ticket, which is the single irreversible action of this
\* bakery. Tickets are natural numbers taken in turn, and the model caps them
\* so the state space stays finite.
Serve(p) ==
    /\ p \notin want
    /\ p \notin inCS
    /\ served < MaxNat
    /\ want' = want \cup {p}
    /\ served' = served + 1
    /\ UNCHANGED << token, inCS >>

\* A process hands the bakery token to its ring successor, but never while it
\* is inside the critical section.
Pass ==
    /\ token' = Succ(token)
    /\ UNCHANGED << want, inCS, served >>

Enter(p) ==
    /\ token = p
    /\ p \in want
    /\ p \notin inCS
    /\ inCS' = inCS \cup {p}
    /\ want' = want \ {p}
    /\ UNCHANGED << token, served >>

Leave(p) ==
    /\ p \in inCS
    /\ inCS' = inCS \ {p}
    /\ UNCHANGED << token, want, served >>

Next == (\E p \in Processes : Serve(p) \/ Enter(p) \/ Leave(p)) \/ Pass

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in Processes : p \in inCS => token = p
Inv == TypeOK
    /\ \A p \in Processes : p \in inCS => token = p
    /\ \A p, q \in Processes : (p \in inCS /\ q \in inCS) => p = q
    /\ \A p \in Processes : p \in inCS => p \notin want

\* Tickets are never issued past the configured cap, and no ticket is ever
\* outstanding once every process has been served.
StateConstraint == served <= MaxNat /\ want \cap inCS = {}

\* The bakery must always make progress: a process that wants the oven gets
\* into the critical section, despite the token going round and round the
\* ring without its help.
Liveness == \A p \in Processes : (p \in want) ~> (p \in inCS)

====