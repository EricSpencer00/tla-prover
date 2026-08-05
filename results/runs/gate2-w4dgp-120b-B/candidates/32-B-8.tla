---- MODULE Chameneos ----
EXTENDS Integers

\* A concurrency game in which chameneoses meet at a shared meeting place
\* (the "mall") and each meeting mutates the colors of the two participants.
\* The game terminates when all chameneoses have faded (after N meetings).
\* It is a faithful transcription of the original specification and the
\* invariants are left untouched: the correction touches only the
\* next-state relation, which mistakenly left some variables unassigned.
=============================================================================