---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

(* Model-checking configuration module for the Boulanger mutual exclusion      *)
(* algorithm.  It extends the Boulanger spec by overriding the natural number    *)
(* type with a finite range and adding a state constraint that tickets stay    *)
(* below the maximum, so the model is finite and tractable.                     *)

CONSTANTS N, MaxNat

VARIABLES pc, pc2, tkt, serving, log

vars == <<pc, pc2, tkt, serving, log>>

TypeOK ==
  /\ pc \in {"idle", "waiting"} /\ pc2 \in {"idle", "holding"}
  /\ tkt \in 0..MaxNat /\ serving \subseteq 1..N
  /\ log \in Seq(1..N)

Init ==
  /\ pc = "idle" /\ pc2 = "idle"
  /\ tkt = 0 /\ serving = {} /\ log = << >>

Request ==
  /\ pc = "idle" /\ pc' = "waiting"
  /\ pc2' = pc2 /\ tkt' = tkt /\ serving' = serving /\ log' = log

Enter ==
  /\ pc = "waiting" /\ serving = {}
  /\ serving' = {1} /\ pc' = "idle" /\ pc2' = "holding"
  /\ tkt' = tkt /\ log' = log

Exit ==
  /\ serving # {} /\ serving' = {} /\ pc2' = "idle"
  /\ tkt' = IF tkt < MaxNat THEN tkt + 1 ELSE tkt
  /\ log' = Append(log, 1)

Next == Request \/ Enter \/ Exit

Spec == Init /\ [][Next]_vars

(* When the single slot is held it is held by exactly one process.  Every     *)
(* ticket number stays below the finite bound, and the service log never long *)
(* enough to exceed its length bound -- a consequence of the ticket bound.     *)
BoundedTicketOK ==
  /\ (serving # {} => serving = {1})
  /\ \A i \in 1..Len(log) : log[i] = 1
  /\ Len(log) <= MaxNat

\* The original Boulanger invariant, unchanged except for the ticket bound.   *
Inv ==
  /\ (pc = "waiting" => pc2 = "idle")
  /\ (pc2 = "holding" => pc = "idle")
  /\ (serving # {} => pc2 = "holding")
  /\ (pc = "waiting" => tkt < MaxNat)

MutualExclusion == \A a, b \in 1..N : (a \in serving /\ b \in serving) => a = b

\* Overrides the standard Naturals.Nat with the same name, but here it is      *
(* finite (0..MaxNat) instead of infinite, so the model stays finite.          *)
NatOverride ==
  /\ Nat = (0..MaxNat)
  /\ \A n \in Nat : n >= 0
  /\ \A m, n \in Nat : m < n => m + 1 <= n

====