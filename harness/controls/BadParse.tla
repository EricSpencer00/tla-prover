---- MODULE BadParse ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ /\  \* deliberate syntax error: dangling conjunction
====
