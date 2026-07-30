---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Commit Protocol (ACP-NB).  The reliable broadcast 
\* implementation forwards a predecision to each participant before delivering 
\* it to the local site.  Since a participant does not forward to itself, the
\* predecision is stored in a "forward" field first, and then delivered.

EXTENDS ACP_SB

================================================================================