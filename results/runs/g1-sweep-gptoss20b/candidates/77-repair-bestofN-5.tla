---- MODULE EWD998Chan_opts ----
EXTENDS EWD998Chan, TLC, IOUtils, CSV

\* The data collection below only works with TLC running in generation mode.
\* Unless TLC runs with -Dtlc2.tool.impl.Tool.probabilistic=true (or -generate),
\* the simulator generates all successor states from which it chooses one randomly. 
\* In "generate" mode, however, TLC randomly generates a (single) successor state.
ASSUME TLCGet("config").mode = "generate"
\* Do not artificially restrict the length of behaviors.
ASSUME TLCGet("config").depth = -1
\* The algorithm terminates. Thus, do not check for deadlocks.
ASSUME TLCGet("config").deadlock = FALSE
\* Require a recent versions of TLC with support for the operators appearing below.
ASSUME TLCGet("revision").timestamp >= 1628119427 

--------------------------------------------------------------------------------

InitSim ==
    /\ active = [n \in Node |-> TRUE]
    /\ color = [n \in Node |-> "white"]

PassTokenOpts(n) ==
  /\ n # 0
  /\ \/ ~ active[n] 
     \/ color[n] = "black"
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "tok"
          /\ LET tkn == inbox[n][j]
             IN  inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
          /\ color' = [color EXCEPT ![n] = "white"]
  /\ UNCHANGED <<active, counter>>

SystemOpts(n) == \/ InitiateProbe
                 \/ PassTokenOpts(n)

SpecOpts == InitSim /\ Init /\ [][\E n \in Node: SystemOpts(n) \/ Environment]_vars

--------------------------------------------------------------------------------

\* No action constraint or additional constraints are required for the model checker.

--------------------------------------------------------------------------------

\* Initialize TLC register.  This is retained for backward compatibility,
\* but it has no effect because TLCSet is no longer used.
ASSUME TLCSet(1, 0)

====