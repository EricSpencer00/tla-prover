---- MODULE MissionariesAndCannibals ----
EXTEND Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------- *)
(*   Sets of banks                                                    *)
(* ------------------------------------------------------------------- *)
Bank == {"East", "West"}

(* ------------------------------------------------------------------- *)
(*   Variables                                                        *)
(* ------------------------------------------------------------------- *)
VARIABLES boat, people

(* ------------------------------------------------------------------- *)
(*   Helper definitions                                               *)
(* ------------------------------------------------------------------- *)
IsMissionary(p) == p \in Missionaries
IsCannibal(p)   == p \in Cannibals

CountMissionaries(set) == Cardinality({p \in set : IsMissionary(p)})
CountCannibals(set)    == Cardinality({p \in set : IsCannibal(p)})

Safe(b) ==
    LET ppl == people[b] IN
    LET m == CountMissionaries(ppl) IN
    LET c == CountCannibals(ppl) IN
    (m = 0) \/ (c <= m)

SafeAll == \A b \in Bank : Safe(b)

(* ------------------------------------------------------------------- *)
(*   Initialization                                                   *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ boat = "East"
    /\ people = [ "East" |-> Missionaries \cup Cannibals,
                  "West" |-> {} ]

(* ------------------------------------------------------------------- *)
(*   Next-state relation                                              *)
(* ------------------------------------------------------------------- *)
Next ==
    \E S \subseteq people[boat] :
        /\ Cardinality(S) \in {1, 2}
        /\ LET dest == IF boat = "East" THEN "West"
                     ELSE "East"
           IN
              /\ boat' = dest
              /\ people' = [people EXCEPT
                              ![boat] = people[boat] \ S,
                              ![dest] = people[dest] \cup S]
              /\ SafeAll'

(* ------------------------------------------------------------------- *)
(*   Type correctness invariant                                       *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ boat \in Bank
    /\ people \in [Bank -> SUBSET (Missionaries \cup Cannibals)]
    /\ UNION {people[b] : b \in Bank} = Missionaries \cup Cannibals
    /\ \A b1, b2 \in Bank : b1 # b2 => people[b1] \cap people[b2] = {}

(* ------------------------------------------------------------------- *)
(*   Solution invariant (east bank empty)                             *)
(* ------------------------------------------------------------------- *)
Solution == people["East"] = {}

(* ------------------------------------------------------------------- *)
(*   Specification (optional)                                         *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<boat, people>>

====