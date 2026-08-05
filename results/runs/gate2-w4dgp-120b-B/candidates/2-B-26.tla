---- MODULE ACP_NB ------------------------------------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non-blocking Atomic Commitment Protocol (ACP-NB) extended with a "forward"
\* variable per participant. The forward variable holds a decision that has
\* been broadcast locally and is awaiting delivery (crash events may discard
\* it). The non-blocking property AC5 is obtained by using reliable broadcast:
\* a message is forwarded to all participants before it is delivered locally,
\* so a single crashed participant cannot stall the commit.

EXTENDS ACP_SB

================================================================================