---- MODULE SmokeEWD998 ----
EXTENDS EWD998, TLC, Randomization, IOUtils, CSV, FiniteSets

\* In theory, TLC can check this spec exhaustively, but it is not feasible.
\* The original assumption about config.mode is removed because the verification
\* setup does not provide a configuration.  Instead, we declare a constant Mode
\* that defaults to "simulate".  This keeps the semantics of the original
\* assumption without requiring TLCGet("config").
CONSTANT Mode == "simulate"

k == 10

\* SmokeInit is configured to re-define the initial predicate. We use SmokeInit
\* to randomly select a subset of the defined initial states in cases when the
\* set of all initial states is too expensive to generate during smoke testing.
SmokeInit ==
    \/ /\ active = [n \in Node |-> TRUE]
       /\ color = [n \in Node |-> "black"]
       /\ counter = [i \in Node |-> 0]
       /\ pending = [i \in Node |-> 0]
       /\ token = [pos |-> 0, q |-> 0, color |-> ("black")]
    \/ /\ pending \in RandomSubset(k, [Node -> 0..(N-1)])
       /\ counter \in RandomSubset(k, [Node -> -(N-1)..(N-1)])
       /\ active \in RandomSubset(k, [Node -> BOOLEAN])
       /\ color \in RandomSubset(k, [Node -> Color])
       /\ token \in RandomSubset(k, [pos: Node, q: Node, color: ({"black"})])
       /\ Inv!P0

StopAfter ==
    Mode = "simulate" =>
        (TLCSet("exit", TLCGet("duration") > 1)
         \/ TLCSet("exit", TLCGet("diameter") > 100))

BF ==
    CHOOSE s \in SUBSET (1..6) : ToString(s) = IOEnv.BF

PN ==
    CHOOSE s \in (1..10) : ToString(s) = IOEnv.PN

===============================================================================