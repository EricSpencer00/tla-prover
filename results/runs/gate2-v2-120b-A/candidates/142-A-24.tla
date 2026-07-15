---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the .cfg file
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*-----------------------------------------------------------------
  State variables (inherited from the sequential algorithm)
-----------------------------------------------------------------*)
VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Nodes = Nodes
Root  = Root

\* The set of all nodes reachable from a given set of start nodes,
\* using only edges that stay within the universe Nodes.
ReachableFrom(start) ==
  LET Rec(s) == s \cup { n \in Nodes : \E m \in s : Edge(m, n) } IN
    CHOOSE r \in SUBSET Nodes :
      /\ start \subseteq r
      /\ \A n \in r : \E m \in r : Edge(m, n) \/ n \in start
      /\ \A s \in SUBSET Nodes :
            /\ start \subseteq s
            /\ \A n \in s : \E m \in s : Edge(m, n) \/ n \in start
            => r \subseteq s

(* Edge relation: example total order to ensure finiteness. *)
Edge(m, n) == n = m + 1

(*-----------------------------------------------------------------
  Type correctness predicate
-----------------------------------------------------------------*)
TypeCorrect ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Mark", "Done"}

(*-----------------------------------------------------------------
  Invariants as described
-----------------------------------------------------------------*)
Inv1 ==
  /\ TypeCorrect
  /\ \A m \in Marked :
        \A n \in Nodes :
          Edge(m, n) => (n \in Marked) \/ (n \in Frontier)

Inv2 ==
  (Marked \cup ReachableFrom(Frontier)) =
    ReachableFrom(Marked \cup Frontier)

Inv3 ==
  ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Mark"

(*-----------------------------------------------------------------
  Transition: deterministic marking step
-----------------------------------------------------------------*)
MarkStep ==
  /\ pc = "Mark"
  /\ \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup
                        { m \in Nodes : Edge(n, m) /\ m \notin Marked }
        /\ pc' = IF Frontier' = {} THEN "Done" ELSE "Mark"

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<Marked, Frontier, pc>>

Next ==
  \/ MarkStep
  \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Theorem stating partial correctness (optional but allowed)
-----------------------------------------------------------------*)
THEOREM TerminationPartialCorrectness ==
  Spec => (pc = "Done") => (Marked = ReachableFrom({Root}))

====