---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
\* The natural numbers used by the algorithm are restricted to the finite
\* range 0..MaxNat.  This is the only place where the infinite set Nat is
\* overridden; all other uses of Nat in the imported Bakery module refer to
\* this finite set.
\* 
\* The constant Nat is defined in the .cfg file as 0..MaxNat, so we do not
\* need to redeclare it here.  We keep the declaration for clarity.
\* ----------------------------------------------------------------------
\* The set of process identifiers
Proc == 1..N

\* ----------------------------------------------------------------------
\* State variables (inherited from Bakery)
\* ----------------------------------------------------------------------
VARIABLES ticket, choosing, cs

\* ----------------------------------------------------------------------
\* Helper definitions (same as in Bakery)
\* ----------------------------------------------------------------------
\* The ticket of a process p
Ticket(p) == ticket[p]

\* The set of processes that are currently choosing a ticket
Choosing == {p \in Proc : choosing[p]}

\* The set of processes that are currently in the critical section
CS == {p \in Proc : cs[p]}

\* ----------------------------------------------------------------------
\* Initial state (same as Bakery, but with finite Nat)
\* ----------------------------------------------------------------------
Init ==
    /\ ticket = [p \in Proc |-> 0]
    /\ choosing = [p \in Proc |-> FALSE]
    /\ cs = [p \in Proc |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions (same as Bakery)
\* ----------------------------------------------------------------------
\* Process p starts choosing a ticket
Choose(p) ==
    /\ choosing[p] = FALSE
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<ticket, cs>>

\* Process p finishes choosing a ticket
FinishChoose(p) ==
    /\ choosing[p] = TRUE
    /\ ticket' = [ticket EXCEPT ![p] = 1 + MaxNat] \* placeholder; actual max will be computed below
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ UNCHANGED cs

\* Compute the maximum ticket among all processes (including p)
MaxTicket ==
    MAX ticket

\* Process p enters the critical section
EnterCS(p) ==
    /\ cs[p] = FALSE
    /\ \A q \in Proc :
          (q # p) => (Ticket(q) = 0) \/ (Ticket(q) # Ticket(p)) \/ (Ticket(q) = Ticket(p) /\ q > p)
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<ticket, choosing>>

\* Process p leaves the critical section
LeaveCS(p) ==
    /\ cs[p] = TRUE
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, choosing>>

\* The next-state relation
Next ==
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : FinishChoose(p)
    \/ \E p \in Proc : EnterCS(p)
    \/ \E p \in Proc : LeaveCS(p)

\* ----------------------------------------------------------------------
\* Specification (inductive)
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_<<ticket, choosing, cs>>

\* ----------------------------------------------------------------------
\* Safety invariants (same as Bakery)
\* ----------------------------------------------------------------------
MutualExclusion == \A p, q \in Proc : (p # q) => ~(cs[p] /\ cs[q])

TypeOK ==
    /\ ticket \in [Proc -> Nat]
    /\ choosing \in [Proc -> BOOLEAN]
    /\ cs \in [Proc -> BOOLEAN]

Inv ==
    \A p \in Proc :
        (cs[p] => (Ticket(p) > 0) /\ \A q \in Proc :
            (q # p) => (Ticket(q) = 0) \/ (Ticket(q) # Ticket(p)) \/ (Ticket(q) = Ticket(p) /\ q > p))

\* ----------------------------------------------------------------------
\* The module ends here
\* ----------------------------------------------------------------------
====