---- MODULE Voting ----
EXTENDS Integers, TLAPS

CONSTANT Value,     \* The set of choosable values.
         Acceptor,  \* A set of processes that will choose a value.
         Quorum     \* The set of "quorums", where a quorum is a 
                    \*   "large enough" set of acceptors

=============================================================================