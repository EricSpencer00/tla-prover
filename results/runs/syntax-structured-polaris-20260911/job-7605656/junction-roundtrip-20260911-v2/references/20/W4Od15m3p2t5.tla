---- MODULE W4Od15m3p2t5 ----
EXTENDS Naturals
CONSTANTS Nodes, Total, MaxTerm
VARIABLES leader, term, up, unmatched, matched
None == "none"
vars == <<leader, term, up, unmatched, matched>>
Init ==
    ( (leader = None)
     /\  (term = 0)
     /\  (up = [n \in Nodes |-> TRUE])
     /\  (unmatched = Total)
     /\  (matched = 0))
Elect(n) ==
    ( (leader = None)
     /\  (up[n])
     /\  (term < MaxTerm)
     /\  (leader' = n)
     /\  (term' = term + 1)
     /\  (UNCHANGED <<up, unmatched, matched>>))
LeaderFail(n) ==
    ( (leader = n)
     /\  (up[n])
     /\  (up' = [up EXCEPT ![n] = FALSE])
     /\  (leader' = None)
     /\  (UNCHANGED <<term, unmatched, matched>>))
NodeFail(n) ==
    ( (up[n])
     /\  (leader # n)
     /\  (up' = [up EXCEPT ![n] = FALSE])
     /\  (UNCHANGED <<leader, term, unmatched, matched>>))
Recover(n) ==
    ( (~up[n])
     /\  (up' = [up EXCEPT ![n] = TRUE])
     /\  (UNCHANGED <<leader, term, unmatched, matched>>))
AdminAppoint(n) ==
    ( (up[n])
     /\  (term < MaxTerm)
     /\  (leader' = n)
     /\  (term' = term + 1)
     /\  (UNCHANGED <<up, unmatched, matched>>))
Match ==
    ( (leader # None)
     /\  (unmatched > 0)
     /\  (unmatched' = unmatched - 1)
     /\  (matched' = matched + 1)
     /\  (UNCHANGED <<leader, term, up>>))
Cancel ==
    ( (matched > 0)
     /\  (matched' = matched - 1)
     /\  (unmatched' = unmatched + 1)
     /\  (UNCHANGED <<leader, term, up>>))
Next ==
    ( (\E n \in Nodes : Elect(n) \/ LeaderFail(n) \/ NodeFail(n) \/ Recover(n) \/ AdminAppoint(n))
     \/  (Match \/ Cancel))
Spec == Init /\ [][Next]_vars
SharesConserved == unmatched + matched = Total
====