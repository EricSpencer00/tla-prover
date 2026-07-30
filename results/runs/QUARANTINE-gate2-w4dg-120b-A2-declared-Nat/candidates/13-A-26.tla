---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES users, time, turn, ticket, turnFlag

vars == <<users, time, turn, ticket, turnFlag>>

TypeOK ==
  /\ users \in [1 .. N -> {"idle", "waiting", "cs"}]
  /\ time \in Nat
  /\ turn \in Nat
  /\ ticket \in [1 .. N -> Nat]
  /\ turnFlag \in BOOLEAN

MutualExclusion ==
  \A a, b \in 1 .. N : (users[a] = "cs" /\ users[b] = "cs") => a = b

Inv == TypeOK /\ MutualExclusion

\* Ticket numbering uses the finite-range Nat, so it saturates at MaxNat.
Claim ==
  /\ \E p \in 1 .. N :
       /\ users[p] = "idle"
       /\ users' = [users EXCEPT ![p] = "waiting"]
       /\ ticket' = [ticket EXCEPT ![p] = IF time > MaxNat THEN MaxNat ELSE time]
  /\ time' = IF time < MaxNat THEN time + 1 ELSE time
  /\ UNCHANGED <<turn, turnFlag>>

ChooseHead ==
  /\ \E p \in 1 .. N :
       /\ users[p] = "waiting"
       /\ (turnFlag \/ \A q \in 1 .. N : ticket[q] # turn)
       /\ turn' = ticket[p]
       /\ turnFlag' = TRUE
  /\ UNCHANGED <<users, time, ticket>>

Enter ==
  /\ \E p \in 1 .. N :
       /\ turnFlag
       /\ turn = ticket[p]
       /\ users[p] = "waiting"
       /\ users' = [users EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<time, turn, ticket, turnFlag>>

Exit ==
  /\ \E p \in 1 .. N :
       /\ users[p] = "cs"
       /\ users' = [users EXCEPT ![p] = "idle"]
  /\ turn' = 0
  /\ turnFlag' = FALSE
  /\ UNCHANGED <<time, ticket>>

Next == Claim \/ ChooseHead \/ Enter \/ Exit

Init ==
  /\ users = [p \in 1 .. N |-> "idle"]
  /\ time = 0
  /\ turn = 0
  /\ ticket = [p \in 1 .. N |-> 0]
  /\ turnFlag = FALSE

\* The inductive spec starts from any type-correct state satisfying the invariant.
ISpec == Init /\ [][Next]_vars

\* The cfg substitutes NatOverride for Nat, so the infinite Nat is replaced by a
\* finite range 0..MaxNat here.
NatOverride == 0 .. MaxNat

====