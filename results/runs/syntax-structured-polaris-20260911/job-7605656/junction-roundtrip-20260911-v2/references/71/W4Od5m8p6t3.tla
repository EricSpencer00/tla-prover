---- MODULE W4Od5m8p6t3 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Clients, Regions, LobbiesPer, RosterLimit, MaxForm, FREE, NOTICKET

Lobbies == [reg: Regions, idx: 1..LobbiesPer]

\* regionLock / lobbyLock: the coarse and fine levels of the scheme.
\* form: each lobby's formation number; ticket: what a client is carrying.
\* roster: seated entries, each stamped with the formation it was seated at.
VARIABLES regionLock, lobbyLock, form, ticket, roster

vars == <<regionLock, lobbyLock, form, ticket, roster>>

Tickets == [lobby: Lobbies, form: 0..MaxForm]
Entries == [who: Clients, form: 0..MaxForm]

TypeOK ==
    ( (regionLock \in [Regions -> Clients \cup {FREE}])
     /\  (lobbyLock \in [Lobbies -> Clients \cup {FREE}])
     /\  (form \in [Lobbies -> 0..MaxForm])
     /\  (ticket \in [Clients -> Tickets \cup {NOTICKET}])
     /\  (roster \in [Lobbies -> SUBSET Entries]))

Init ==
    ( (regionLock = [r \in Regions |-> FREE])
     /\  (lobbyLock = [l \in Lobbies |-> FREE])
     /\  (form = [l \in Lobbies |-> 0])
     /\  (ticket = [c \in Clients |-> NOTICKET])
     /\  (roster = [l \in Lobbies |-> {}]))

TakeRegion(c, r) ==
    ( (regionLock[r] = FREE)
     /\  (ticket[c] = NOTICKET)
     /\  (regionLock' = [regionLock EXCEPT ![r] = c])
     /\  (UNCHANGED <<lobbyLock, form, ticket, roster>>))

\* The fine lock is taken under the coarse one, which is dropped at once.
TakeLobby(c, l) ==
    ( (regionLock[l.reg] = c)
     /\  (lobbyLock[l] = FREE)
     /\  (ticket[c] = NOTICKET)
     /\  (lobbyLock' = [lobbyLock EXCEPT ![l] = c])
     /\  (regionLock' = [regionLock EXCEPT ![l.reg] = FREE])
     /\  (ticket' = [ticket EXCEPT ![c] = [lobby |-> l, form |-> form[l]]])
     /\  (UNCHANGED <<form, roster>>))

Seat(c) ==
    ( (ticket[c] # NOTICKET)
     /\  (LET tk == ticket[c] IN
        ( (form[tk.lobby] = tk.form)
         /\  (Cardinality(roster[tk.lobby]) < RosterLimit)
         /\  (roster' = [roster EXCEPT ![tk.lobby] =
                        @ \cup {[who |-> c, form |-> tk.form]}])
         /\  (lobbyLock' = [lobbyLock EXCEPT ![tk.lobby] = FREE])))
     /\  (ticket' = [ticket EXCEPT ![c] = NOTICKET])
     /\  (UNCHANGED <<regionLock, form>>))

Scrap(c) ==
    ( (ticket[c] # NOTICKET)
     /\  (form[ticket[c].lobby] # ticket[c].form)
     /\  (lobbyLock' = [lobbyLock EXCEPT ![ticket[c].lobby] = FREE])
     /\  (ticket' = [ticket EXCEPT ![c] = NOTICKET])
     /\  (UNCHANGED <<regionLock, form, roster>>))

\* Re-forming does not wait for whoever is sitting on the lobby's lock.
Reform(l) ==
    ( (form[l] < MaxForm)
     /\  (form' = [form EXCEPT ![l] = @ + 1])
     /\  (roster' = [roster EXCEPT ![l] = {}])
     /\  (UNCHANGED <<regionLock, lobbyLock, ticket>>))

Leave(l, e) ==
    ( (e \in roster[l])
     /\  (roster' = [roster EXCEPT ![l] = @ \ {e}])
     /\  (UNCHANGED <<regionLock, lobbyLock, form, ticket>>))

Next ==
    ( (\E c \in Clients, r \in Regions : TakeRegion(c, r))
     \/  (\E c \in Clients, l \in Lobbies : TakeLobby(c, l))
     \/  (\E c \in Clients : Seat(c) \/ Scrap(c))
     \/  (\E l \in Lobbies : Reform(l) \/ (\E e \in roster[l] : Leave(l, e))))

Spec == Init /\ [][Next]_vars

RosterMatchesCurrentFormation ==
    \A l \in Lobbies : \A e \in roster[l] : e.form = form[l]
====