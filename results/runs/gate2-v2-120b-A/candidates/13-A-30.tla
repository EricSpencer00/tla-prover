---- MODULE MCBakery ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Configuration constants (to be assigned concrete values in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
PROCESS == 1..N

\* ----------------------------------------------------------------------
\* State variables (inherited from the Bakery specification)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, entering

\* pc[p]   : the program counter (control state) of process p
\* ticket[p]: the ticket number of process p (if any)
\* entering[p]: boolean flag indicating if process p is in the "choosing" phase

\* ----------------------------------------------------------------------
\* Types and type-correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [PROCESS -> {"idle", "choose", "wait", "cs", "exit"}]
    /\ ticket \in [PROCESS -> Nat]
    /\ entering \in [PROCESS -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state (same as Bakery's Init, respecting the finite Nat range)
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in PROCESS |-> "idle"]
    /\ ticket = [p \in PROCESS |-> 0]
    /\ entering = [p \in PROCESS |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions (exactly those of the Bakery algorithm)
\* ----------------------------------------------------------------------
\* 1. Non‑critical work (idle → choose)
Idle(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<ticket, entering>>

\* 2. Choose a ticket number (choose → wait)
Choose(p) ==
    /\ pc[p] = "choose"
    /\ entering' = [entering EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] =
          1 + Max({ ticket[q] : q \in PROCESS })]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<pc, entering>>

\* 3. Finish choosing (wait → cs) – wait until it is this process's turn
EnterCS(p) ==
    /\ pc[p] = "wait"
    /\ entering' = [entering EXCEPT ![p] = FALSE]
    /\ \A q \in PROCESS :
          (q # p) =>
            ( \/ entering[q] = FALSE
               \/ (ticket[q] = 0)
               \/ ( (ticket[p] < ticket[q])
                    \/ (ticket[p] = ticket[q] /\ p < q) )
            )
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<ticket, entering>>

\* 4. Exit critical section (cs → exit)
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<ticket, entering>>

\* 5. Reset after exit (exit → idle)
Reset(p) ==
    /\ pc[p] = "exit"
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED entering

\* ----------------------------------------------------------------------
\* Stuttering step to allow deadlock‑free model checking (even though deadlock
\* checking is disabled, it does not hurt to include it)
\* ----------------------------------------------------------------------
Stutter ==
    UNCHANGED <<pc, ticket, entering>>

\* ----------------------------------------------------------------------
\* Next-state relation (any enabled action of any process, or stutter)
\* ----------------------------------------------------------------------
Next ==
    \E p \in PROCESS :
        \/ Idle(p)
        \/ Choose(p)
        \/ EnterCS(p)
        \/ ExitCS(p)
        \/ Reset(p)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification: inductive start (any state satisfying the invariant)
\* ----------------------------------------------------------------------
ISpec ==
    /\ TypeOK
    /\ [][Next]_<<pc, ticket, entering>>

\* ----------------------------------------------------------------------
\* Safety invariant: mutual exclusion (no two processes in CS simultaneously)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A p, q \in PROCESS :
        (p # q) => ~ (pc[p] = "cs" /\ pc[q] = "cs")

\* ----------------------------------------------------------------------
\* Full inductive invariant (state‑correctness + safety)
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ MutualExclusion

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
ASSUME SpecIsISpec == ISpec
SPECIFICATION ISpec
INVARIANT Inv
INVARIANT MutualExclusion
INVARIANT TypeOK

====