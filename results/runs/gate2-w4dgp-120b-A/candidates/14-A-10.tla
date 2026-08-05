---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

VARIABLES ticket, wants, turn, cs

vars == <<ticket, wants, turn, cs>>

\* Finite override: Nat is replaced by a finite version limited to MaxNat.
Nat == 0 .. MaxNat

InRange == \A i \in 1 .. N : ticket[i] < MaxNat

TypeOK ==
  /\ ticket \in [1 .. N -> Nat]
  /\ wants \in [1 .. N -> BOOLEAN]
  /\ turn \in 1 .. N
  /\ cs \in 0 .. N

Init ==
  /\ ticket = [i \in 1 .. N |-> 0]
  /\ wants = [i \in 1 .. N |-> FALSE]
  /\ turn = 1
  /\ cs = 0

Request(i) ==
  /\ ~wants[i]
  /\ wants' = [wants EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, turn, cs>>

Allocate(i) ==
  /\ wants[i]
  /\ ticket[i] < MaxNat - 1
  /\ ticket' = [ticket EXCEPT ![i] = ticket[i] + 1]
  /\ wants' = [wants EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<turn, cs>>

Enter(i) ==
  /\ ticket[i] > 0
  /\ turn = i
  /\ cs = 0
  /\ cs' = i
  /\ UNCHANGED <<ticket, wants, turn>>

Exit(i) ==
  /\ cs = i
  /\ cs' = 0
  /\ turn' = (turn % N) + 1
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED wants

Next ==
  \/ \E i \in 1 .. N : Request(i)
  \/ \E i \in 1 .. N : Allocate(i)
  \/ \E i \in 1 .. N : Enter(i)
  \/ \E i \in 1 .. N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i, j \in 1 .. N : (cs = i /\ cs = j) => (i = j)

Inv ==
  /\ (cs = 0) \/ (cs \in 1 .. N)
  /\ (cs = 0) \/ (ticket[cs] > 0)

====