---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Commit Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message, this message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to 
\*     store the decision before it's delivered (and becomes "decision")

EXTENDS ACP_SB

================================================================================