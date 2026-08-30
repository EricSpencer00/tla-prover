---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers for the TLA+ proof system. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Temporal-logic proof rules from Lamport's "The Temporal Logic of Actions". *)
CONSTANTS InvarianceRule, WellFormednessRule, StrongFairnessRule, WeakFairnessRule, StepSimulationRule, NoLiveStateReached

(* Backends that have already been invoked; a one-shot dispatch set, never cleared. *)
VARIABLES dispatched

vars == <<dispatched>>

TypeOK ==
    /\ Zenon \in Nat
    /\ Isabelle \in Nat
    /\ CVC3 \in Nat
    /\ Yices \in Nat
    /\ VeriT \in Nat
    /\ Z3 \in Nat
    /\ SPASS \in Nat
    /\ LS4 \in Nat
    /\ InvarianceRule \in Nat
    /\ WellFormednessRule \in Nat
    /\ StrongFairnessRule \in Nat
    /\ WeakFairnessRule \in Nat
    /\ StepSimulationRule \in Nat
    /\ NoLiveStateReached \in Nat
    /\ dispatched \subseteq (1..9)

Init ==
    /\ Zenon = 0
    /\ Isabelle = 0
    /\ CVC3 = 0
    /\ Yices = 0
    /\ VeriT = 0
    /\ Z3 = 0
    /\ SPASS = 0
    /\ LS4 = 0
    /\ InvarianceRule = 0
    /\ WellFormednessRule = 0
    /\ StrongFairnessRule = 0
    /\ WeakFairnessRule = 0
    /\ StepSimulationRule = 0
    /\ NoLiveStateReached = 0
    /\ dispatched = {}

DispatchBackend(id) ==
    /\ id \notin dispatched
    /\ dispatched' = dispatched \cup {id}
    /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4,
                    InvarianceRule, WellFormednessRule, StrongFairnessRule,
                    WeakFairnessRule, StepSimulationRule, NoLiveStateReached>>

DispatchRule(id) ==
    /\ id \notin dispatched
    /\ dispatched' = dispatched \cup {id}
    /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4,
                    InvarianceRule, WellFormednessRule, StrongFairnessRule,
                    WeakFairnessRule, StepSimulationRule, NoLiveStateReached>>

SPECIFICATION == Init /\ [][DispatchBackend |-> DispatchBackend]_vars /\ [][DispatchRule |-> DispatchRule]_vars

INVARIANTS ==
    /\ \A x \in dispatched : x \in 1..9
    /\ \A x \in dispatched : x = 1 => InvarianceRule = 0
    /\ \A x \in dispatched : x = 2 => WellFormednessRule = 0
    /\ \A x \in dispatched : x = 3 => StrongFairnessRule = 0
    /\ \A x \in dispatched : x = 4 => WeakFairnessRule = 0
    /\ \A x \in dispatched : x = 5 => StepSimulationRule = 0
    /\ \A x \in dispatched : x = 6 => NoLiveStateReached = 0

PROPERTIES ==
    /\ \A S \in (SUBSET Nat) : (\A x \in S : \A y \in S : x = y) => \E x \in S : TRUE
    /\ \A S \in (SUBSET Nat) : (\A x, y \in S : x = y) => S \subseteq Nat /\ Cardinality(S) <= 1

====