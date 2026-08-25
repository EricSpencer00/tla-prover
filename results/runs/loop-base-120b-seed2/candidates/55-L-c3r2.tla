---- MODULE MCEcho ----
EXTENDS Echo

\*--------------------------------------------------------------------
\* Constants required by the Echo specification (instantiated via .cfg)
\*--------------------------------------------------------------------
CONSTANTS Node, initiator, R

\*--------------------------------------------------------------------
\* Concrete instances used by the model checker (substituted via .cfg)
\*--------------------------------------------------------------------
N1 == {"n1", "n2", "n3"}                               \* concrete node set
I1 == "n1"                                            \* deterministic initiator
R1 == { << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >> }          \* fully‑meshed adjacency

\*--------------------------------------------------------------------
\* Specification alias required by the .cfg file
\*--------------------------------------------------------------------
TestSpec == Spec
====