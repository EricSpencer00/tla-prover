---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished root node (Root \\in Nodes)
    Succ     \* Succ[n] is the set of successor nodes of n (Succ \\in [Nodes -> SUBSET Nodes])

\*=====================================================================
\*  Operators required by the configuration
\*=====================================================================

\* A finite version of Seq (here simply aliasing Seq, which already
\* denotes finite sequences of elements of Nodes)
LimitedSeq == Seq(Nodes)

\* Operator that will be substituted for Succ in the configuration.
\* It simply forwards to the constant Succ.
ConnectedToSomeButNotAll(n) == Succ[n]

\*=====================================================================
\*  PlusCal algorithm (translation yields Init, Next, vars)
\*=====================================================================
(*--algorithm ReachableAlg
variables
    marked = {},
    frontier = {Root};

begin
  while (frontier # {}) do
    with n \in frontier do
      if (n \notin marked) then
        marked := marked \cup {n};
        frontier := frontier \cup Succ[n];
      else
        frontier := frontier \setminus {n};
      end if;
    end with;
  end while;
end algorithm; *)
\*=====================================================================
\*  Translation of the PlusCal algorithm
\*=====================================================================

VARIABLES marked, frontier

vars == <<marked, frontier>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}

Next ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ UNCHANGED << >>
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \setminus {n}
          /\ UNCHANGED << >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\*=====================================================================
\*  Invariants
\*=====================================================================

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Helper definition: the set of nodes reachable from a given set S
ReachableFrom(S) ==
    { m \in Nodes :
        \E p \in LimitedSeq :
            /\ Len(p) >= 1
            /\ p[1] \in S
            /\ p[Len(p)] = m
            /\ \A i \in 1..Len(p)-1 : p[i+1] \in Succ[p[i]]
    }

\* Invariant relating marked, frontier and reachability
Inv2 ==
    ReachableFrom(marked) \cup ReachableFrom(frontier) =
        ReachableFrom(marked \cup frontier)

\* Invariant stating that the set of nodes reachable from Root
\* is exactly marked plus what can be reached from the frontier
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    (frontier = {} => marked = ReachableFrom({Root}))

\*=====================================================================
\*  Liveness property
\*=====================================================================
Termination == <> (frontier = {})

====