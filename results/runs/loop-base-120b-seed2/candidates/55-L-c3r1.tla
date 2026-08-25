---- MODULE MCEcho ----
EXTENDS Echo

\*--------------------------------------------------------------------
\* Constants required by the Echo specification
\*--------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\*--------------------------------------------------------------------
\* Concrete instances used by the model checker (substituted via .cfg)
\*--------------------------------------------------------------------
N1 == {"n1", "n2", "n3"}                                 \* concrete node set
I1 == "n1"                                                \* deterministic initiator
R1 == { << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >> }           \* fully‑meshed adjacency
NoNode == "None"                                          \* sentinel distinct from nodes

\*--------------------------------------------------------------------
\* Specification alias required by the .cfg file
\*--------------------------------------------------------------------
TestSpec == Spec

\*--------------------------------------------------------------------
\* Export the invariants expected by the .cfg file.
\* They are defined in the extended Echo module; we expose them here
\* as aliases so that TLC can locate the identifiers.
\*--------------------------------------------------------------------
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
====