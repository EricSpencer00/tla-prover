---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  \E, \F, \G, \H, \I, \J, \K, \L

IsaZenon == [command |-> "zenon -t 2"]
IsaIsabelle == [command |-> "isabelle -t 2"]
IsaCVC3 == [command |-> "cvc3 -t 2"]
IsaYices == [command |-> "yices -t 2"]
IsaVerit == [command |-> "verit -t 2"]
IsaZ3 == [command |-> "z3 -t 2"]
IsaSPASS == [command |-> "spass -t 2"]
IsaLS4 == [command |-> "ls4 -t 2"]

\Axiom == "set extensionality"
\Wf == "no set contains every value"

NoSpec == TRUE

====