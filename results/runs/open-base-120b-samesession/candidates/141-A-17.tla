---- MODULE Reachable ----
EXTENDS Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,          \* The set of all graph nodes
    Root,           \* The distinguished start node (Root \\in Nodes)
    Succ            \* A total function Nodes -> SUBSET Nodes giving successors

==============================================================================