---- MODULE W4Od9m3p6t0 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Controllers, MaxTerm

VARIABLES term, leader, crashed, followers

vars == <<term, leader, crashed, followers>>

Init ==
  /\ term = 0
  /\ leader = [ ]
  /\ crashed = [ ]
  /\ followers = Controllers

Next ==
  /\ term' = IF leader' = leader THEN term + 1 ELSE term
  /\ leader' = IF \E c \in Controllers : c \notin crashed /\ term + 1 = c.term /\ leader = [ ] \/ leader = [c]
                      THEN [c] ELSE leader
  /\ crashed' = crashed \ { c : c \in crashed /\ c \notin crashed }
  /\ followers' = followers \ { c : c \in crashed /\ c \notin crashed } \cup { c : c \in Controllers /\ c \notin crashed /\ c \notin leader /\ c \notin followers }

Spec == Init /\ [][Next]_vars

LeaderAuthorized == term = leader[1].term /\ leader = [leader[1]]

====