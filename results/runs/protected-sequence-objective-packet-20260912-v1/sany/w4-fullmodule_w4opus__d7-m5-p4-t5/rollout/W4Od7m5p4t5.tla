---- MODULE W4Od7m5p4t5 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Bays, Slots, Voters

VARIABLES bayState, voteTally, pendingProposals, adminPlace, containerState

vars == <<bayState, voteTally, pendingProposals, adminPlace, containerState>>

TypeOK ==
    /\ bayState \in [Bays -> [Slots -> {Occupied, Free}]]
    /\ voteTally \in [Bays -> [Slots -> [Voters -> {Approved, NotApproved}]]]
    /\ pendingProposals \in [Slots -> [Voters -> {Proposed, Withdrawn}]]
    /\ adminPlace \in [Slots -> {Proposed, Occupied}]
    /\ containerState \in [Slots -> {Occupied, Free}]

Init ==
    /\ bayState = [b \in Bays |-> [s \in Slots |-> Free]]
    /\ voteTally = [b \in Bays |-> [s \in Slots |-> [v \in Voters |-> NotApproved]]]
    /\ pendingProposals = [s \in Slots |-> [v \in Voters |-> Withdrawn]]
    /\ adminPlace = [s \in Slots |-> Free]
    /\ containerState = [s \in Slots |-> Free]

Propose(b, s) ==
    /\ bayState' = [b' \in Bays |-
        IF b' = b
        THEN [s' \in Slots |-
            IF s' = s
            THEN [Occupied]
            ELSE [bayState[b][s']]
        ELSE bayState[b']
        ]
    ]
    /\ voteTally' = [b' \in Bays |-
        IF b' = b
        THEN [s' \in Slots |-
            IF s' = s
            THEN [v \in Voters |-
                IF v \notin pendingProposals[s]
                THEN Approved
                ELSE NotApproved
                ]
            ELSE voteTally[b][s']
            ]
        ELSE voteTally[b']
        ]
    /\ pendingProposals' = [s' \in Slots |-
        IF s' = s
        THEN [v \in Voters |-
            IF v \notin pendingProposals[s]
            THEN Proposed
            ELSE Withdrawn
            ]
        ELSE pendingProposals[s']
        ]
    /\ adminPlace' = adminPlace
    /\ containerState' = containerState
    /\ UNCHANGED <<bayState, voteTally, pendingProposals, adminPlace>>

Vote(b, s, v) ==
    /\ bayState' = bayState
    /\ voteTally' = [b' \in Bays |-
        IF b' = b
        THEN [s' \in Slots |-
            IF s' = s
            THEN [v' \in Voters |-
                IF v' = v
                THEN Approved
                ELSE NotApproved
                ]
            ELSE voteTally[b][s']
            ]
        ELSE voteTally[b']
        ]
    /\ pendingProposals' = pendingProposals
    /\ adminPlace' = adminPlace
    /\ containerState' = containerState
    /\ UNCHANGED <<bayState, voteTally, pendingProposals>>

Place(b, s) ==
    /\ bayState' = [b' \in Bays |-
        IF b' = b
        THEN [s' \in Slots |-
            IF s' = s
            THEN [Occupied]
            ELSE [bayState[b][s']]
            ]
        ELSE bayState[b']
        ]
    /\ voteTally' = [b' \in Bays |-
        IF b' = b
        THEN [s' \in Slots |-
            IF s' = s
            THEN [v \in Voters |-
                IF v \in pendingProposals[s] /\ [v \in Voters |-> Approved] \subseteq voteTally[b][s]
                THEN Approved
                ELSE NotApproved
                ]
            ELSE voteTally[b][s']
            ]
        ELSE voteTally[b']
        ]
    /\ pendingProposals' = [s' \in Slots |-
        IF s' = s
        THEN [v \in Voters |-
            IF v \in pendingProposals[s]
            THEN Withdrawn
            ELSE Withdrawn
            ]
        ELSE pendingProposals[s']
        ]
    /\ adminPlace' = adminPlace
    /\ containerState' = [s' \in Slots |-
        IF s' = s
        THEN Occupied
        ELSE containerState[s']
        ]
    /\ UNCHANGED <<bayState, voteTally, pendingProposals>>

Withdraw(b, s) ==
    /\ bayState' = bayState
    /\ voteTally' = voteTally
    /\ pendingProposals' = [s' \in Slots |-
        IF s' = s
        THEN [v \in Voters |-
            IF v \in pendingProposals[s]
            THEN Withdrawn
            ELSE Withdrawn
            ]
        ELSE pendingProposals[s']
        ]
    /\ adminPlace' = adminPlace
    /\ containerState' = containerState
    /\ UNCHANGED <<bayState, voteTally, pendingProposals>>

AdminPlace(b, s) ==
    /\ bayState' = [b' \in Bays |-
        IF b' = b
        THEN [s' \in Slots |-
            IF s' = s
            THEN [Occupied]
            ELSE [bayState[b][s']]
            ]
        ELSE bayState[b']
        ]
    /\ voteTally' = voteTally
    /\ pendingProposals' = pendingProposals
    /\ adminPlace' = [s' \in Slots |-
        IF s' = s
        THEN Occupied
        ELSE adminPlace[s']
        ]
    /\ containerState' = [s' \in Slots |-
        IF s' = s
        THEN Occupied
        ELSE containerState[s']
        ]
    /\ UNCHANGED <<bayState, voteTally, pendingProposals>>

Remove(b, s) ==
    /\ bayState' = [b' \in Bays |-
        IF b' = b
        THEN [s' \in Slots |-
            IF s' = s
            THEN [Free]
            ELSE [bayState[b][s']]
            ]
        ELSE bayState[b']
        ]
    /\ voteTally' = voteTally
    /\ pendingProposals' = pendingProposals
    /\ adminPlace' = adminPlace
    /\ containerState' = [s' \in Slots |-
        IF s' = s
        THEN Free
        ELSE containerState[s']
        ]
    /\ UNCHANGED <<bayState, voteTally, pendingProposals>>

Next ==
    \/ Propose(b, s) \/ Vote(b, s, v) \/ Place(b, s) \/ Withdraw(b, s) \/ AdminPlace(b, s) \/ Remove(b, s)

Spec == Init /\ [][Next]_vars

BayPartition ==
    \A b \in Bays, s \in Slots :
        s \in bayState[b] \leftrightarrow (s \in containerState)