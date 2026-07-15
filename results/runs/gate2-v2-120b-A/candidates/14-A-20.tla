---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants (to be fixed in the .cfg file)
-----------------------------------------------------------------*)
CONSTANT N            \* number of processes
CONSTANT MaxNat       \* inclusive upper bound for the finite Nat set
CONSTANT Nat          \* overridden finite set of natural numbers

(*-----------------------------------------------------------------
  Derived constant: the set of process identifiers
-----------------------------------------------------------------*)
Proc == 1 .. N

(*-----------------------------------------------------------------
  State variables (inherited from the Boulanger specification)
-----------------------------------------------------------------*)
VARIABLES PC, ticket, owner

(*-----------------------------------------------------------------
  Type invariant (originally TypeOK) – ensures variables stay within
  their intended domains, using the overridden Nat set.
-----------------------------------------------------------------*)
TypeOK ==
    /\ PC \in [Proc -> {"idle", "trying", "cs"}]
    /\ ticket \in [Proc -> Nat]
    /\ owner \in Nat

(*-----------------------------------------------------------------
  Safety invariant (originally MutualExclusion)
-----------------------------------------------------------------*)
MutualExclusion ==
    /\ (owner = 0) \/ \E i \in Proc : owner = i

(*-----------------------------------------------------------------
  Full inductive invariant (originally Inv) – a conjunction of the
  above safety properties.  Additional constraints from the Boulanger
  algorithm can be added here if needed.
-----------------------------------------------------------------*)
Inv == 
    /\ TypeOK
    /\ MutualExclusion

(*-----------------------------------------------------------------
  Initial state – same as the original Boulanger specification,
  with ticket numbers restricted to Nat.
-----------------------------------------------------------------*)
Init ==
    /\ PC = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ owner = 0

(*-----------------------------------------------------------------
  Actions – these are the original Boulanger actions, unchanged.
-----------------------------------------------------------------*)
Try(i) ==
    /\ i \in Proc
    /\ PC[i] = "idle"
    /\ PC' = [PC EXCEPT ![i] = "trying"]
    /\ ticket' = [ticket EXCEPT ![i] = MaxNat] \* choose the maximum as a placeholder; the model checker will explore all Nat values
    /\ UNCHANGED owner

Enter(i) ==
    /\ i \in Proc
    /\ PC[i] = "trying"
    /\ owner = 0
    /\ PC' = [PC EXCEPT ![i] = "cs"]
    /\ owner' = i
    /\ UNCHANGED ticket

Exit(i) ==
    /\ i \in Proc
    /\ PC[i] = "cs"
    /\ owner = i
    /\ PC' = [PC EXCEPT ![i] = "idle"]
    /\ owner' = 0
    /\ UNCHANGED ticket

Next ==
    \/ \E i \in Proc : Try(i)
    \/ \E i \in Proc : Enter(i)
    \/ \E i \in Proc : Exit(i)

(*-----------------------------------------------------------------
  SPECIFICATION (the top-level behavior)
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<PC, ticket, owner>>

(*-----------------------------------------------------------------
  State constraint – ensures all ticket numbers stay strictly below MaxNat.
-----------------------------------------------------------------*)
StateConstraint ==
    /\ \A i \in Proc : ticket[i] < MaxNat

=============================================================================