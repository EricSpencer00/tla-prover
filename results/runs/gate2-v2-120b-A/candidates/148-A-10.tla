---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (as required by the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,               \* the set of all possible block hashes
    NoHashVal,          \* sentinel value meaning "no hash"
    PrivateKey,         \* set of private keys
    PublicKey,          \* set of public keys
    Node,               \* set of network nodes
    GenesisBalance,     \* total supply of coins (a natural number)
    NoBlockVal,         \* sentinel representing the absence of a block
    CalculateHash,      \* abstract hash operator
    NoHash,             \* alias for NoHashVal (required by .cfg)
    NoBlock             \* alias for NoBlockVal (required by .cfg)

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
Account == PublicKey

BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

\* A block is a record.  For simplicity we do not model the full binary
\* structure of Ed25519 signatures; we only store the signer’s public key.
Block ==
    [type           : BlockType,
     hash           : Hash,
     prevHash       : Hash,
     sender         : Account,
     receiver       : Account,
     amount         : Nat,
     signature      : PublicKey,
     representative : Account]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the most recent block hash known to the system
    Ledger,     \* [node \in Node -> [h \in Hash -> Block \cup {NoBlockVal}]]
    Received    \* [node \in Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Type definitions (used by the TypeInvariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ Ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
    /\ Received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
\* Determine the owner (account) of a block by its type
Owner(b) ==
    IF b.type = "Genesis" THEN b.sender
    ELSE IF b.type = "Send"    THEN b.sender
    ELSE IF b.type = "Open"   THEN b.receiver
    ELSE IF b.type = "Receive" THEN b.receiver
    ELSE IF b.type = "Change" THEN b.sender
    ELSE NoBlockVal

\* Balance of an account as seen on a particular node, by walking its chain
\* (recursive definition using a simple fix‑point)
Balance(node, acct) ==
    LET
        Rec(h) ==
            IF h = NoHashVal THEN 0
            ELSE
                LET b == Ledger[node][h] IN
                IF b = NoBlockVal THEN 0
                ELSE
                    CASE b.type = "Genesis"   -> b.amount
                     [] b.type = "Send"      -> Rec(b.prevHash) - b.amount
                     [] b.type = "Open"      -> b.amount
                     [] b.type = "Receive"   -> Rec(b.prevHash) + b.amount
                     [] b.type = "Change"    -> Rec(b.prevHash)
                     [] OTHER                -> Rec(b.prevHash)
    IN
        IF acct \in Account THEN
            IF b \in DOMAIN Ledger[node] THEN
                \E h \in HASHES : /\ Ledger[node][h] # NoBlockVal
                                 /\ Owner(Ledger[node][h]) = acct
                                 /\ b = Ledger[node][h]
                                 /\ Rec(h) = Rec(h)   \* just to force existence
            ELSE 0
        ELSE 0

\* The set of all hash values that actually appear in any ledger
UsedHashes(node) == { h \in Hash : Ledger[node][h] # NoBlockVal }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E pk \in PrivateKey :
          /\ LET pub == PubOf[pk] IN
             LET g == [type           |-> "Genesis",
                       hash           |-> h,
                       prevHash       |-> NoHashVal,
                       sender         |-> pub,
                       receiver       |-> pub,
                       amount         |-> GenesisBalance,
                       signature      |-> pub,
                       representative |-> pub] IN
                /\ h \in Hash \ {NoHashVal}
                /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = g]]
                /\ lastHash' = h
                /\ Received' = Received
                /\ UNCHANGED <<>>
          /\ UNCHANGED <<>>
          /\ UNCHANGED <<>>

CreateSend ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, pk \in PrivateKey, amt \in Nat :
          /\ pk \in OwnedKey[n]
          /\ LET pub == PubOf[pk] IN
             /\ Ledger[n][lastHash] # NoBlockVal
             /\ Owner(Ledger[n][lastHash]) = pub
             /\ Balance(n, pub) >= amt
             /\ \E recv \in Account :
                    LET h == CalculateHash([type |-> "Send",
                                            prevHash |-> lastHash,
                                            sender   |-> pub,
                                            receiver |-> recv,
                                            amount   |-> amt,
                                            representative |-> Ledger[n][lastHash].representative]) IN
                    /\ h \in Hash \ {NoHashVal}
                    /\ Ledger' = [n2 \in Node |-
                                    [ Ledger[n2] EXCEPT ![h] =
                                        [type           |-> "Send",
                                         hash           |-> h,
                                         prevHash       |-> lastHash,
                                         sender         |-> pub,
                                         receiver       |-> recv,
                                         amount         |-> amt,
                                         signature      |-> pub,
                                         representative |-> Ledger[n][lastHash].representative] ] ]
                    /\ lastHash' = h
                    /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
                    /\ UNCHANGED <<>>

CreateOpen ==
    /\ \E n \in Node, pk \in PrivateKey :
          /\ pk \in OwnedKey[n]
          /\ LET pub == PubOf[pk] IN
             /\ \E sendHash \in Received[n] :
                    LET sb == Ledger[n][sendHash] IN
                    /\ sb.type = "Send"
                    /\ sb.receiver = pub
                    /\ \E h \in Hash :
                           /\ h \notin UsedHashes(n)
                           /\ LET b == [type           |-> "Open",
                                        hash           |-> h,
                                        prevHash       |-> NoHashVal,
                                        sender         |-> pub,
                                        receiver       |-> pub,
                                        amount         |-> sb.amount,
                                        signature      |-> pub,
                                        representative |-> sb.representative] IN
                            /\ Ledger' = [n2 \in Node |-
                                            [ Ledger[n2] EXCEPT ![h] = b ]]
                            /\ Received' = [n2 \in Node |-> Received[n2] \ {sendHash}]
                            /\ UNCHANGED lastHash

CreateReceive ==
    /\ \E n \in Node, pk \in PrivateKey :
          /\ pk \in OwnedKey[n]
          /\ LET pub == PubOf[pk] IN
             /\ \E sendHash \in UsedHashes(n) :
                   LET sb == Ledger[n][sendHash] IN
                   /\ sb.type = "Send"
                   /\ sb.receiver = pub
                   /\ Ledger[n][lastHash] # NoBlockVal
                   /\ Owner(Ledger[n][lastHash]) = pub
                   /\ \E h \in Hash :
                          /\ h \notin UsedHashes(n)
                          /\ LET b == [type           |-> "Receive",
                                       hash           |-> h,
                                       prevHash       |-> lastHash,
                                       sender         |-> sb.sender,
                                       receiver       |-> pub,
                                       amount         |-> sb.amount,
                                       signature      |-> pub,
                                       representative |-> Ledger[n][lastHash].representative] IN
                               /\ Ledger' = [n2 \in Node |-
                                               [ Ledger[n2] EXCEPT ![h] = b ]]
                               /\ lastHash' = h
                               /\ Received' = [n2 \in Node |-> Received[n2] \ {sendHash}]
                               /\ UNCHANGED <<>>

CreateChange ==
    /\ \E n \in Node, pk \in PrivateKey, newRep \in Account :
          /\ pk \in OwnedKey[n]
          /\ LET pub == PubOf[pk] IN
             /\ Ledger[n][lastHash] # NoBlockVal
             /\ Owner(Ledger[n][lastHash]) = pub
             /\ \E h \in Hash :
                    /\ h \notin UsedHashes(n)
                    /\ LET b == [type           |-> "Change",
                                 hash           |-> h,
                                 prevHash       |-> lastHash,
                                 sender         |-> pub,
                                 receiver       |-> pub,
                                 amount         |-> 0,
                                 signature      |-> pub,
                                 representative |-> newRep] IN
                         /\ Ledger' = [n2 \in Node |-
                                         [ Ledger[n2] EXCEPT ![h] = b ]]
                         /\ lastHash' = h
                         /\ UNCHANGED Received

\* Broadcast of a newly created block to all nodes' Received sets
Broadcast(hash) ==
    /\ Received' = [n \in Node |-> Received[n] \cup {hash}]
    /\ UNCHANGED <<lastHash, Ledger>>

\* Validation of a single received block at a node
Validate(node) ==
    /\ \E h \in Received[node] :
          LET b == Ledger[node][h] IN
          /\ b # NoBlockVal
          /\ b.signature = Owner(b)                     \* abstract signature check
          /\ (b.type = "Send" => b.prevHash \in UsedHashes(node))
          /\ (b.type \in {"Open","Receive","Change"} => b.prevHash \in UsedHashes(node))
          /\ Ledger' = Ledger
          /\ Received' = [node \in Node |-> IF node = node THEN Received[node] \ {h}
                                             ELSE Received[node]]
          /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ \E h \in Hash : Broadcast(h)
    \/ \E n \in Node : Validate(n)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, Ledger, Received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant == TypeOK

SafetyInvariant ==
    /\ TypeOK
    /\ \A n \in Node :
          \A h \in HASHES :
             LET b == Ledger[n][h] IN
                IF b = NoBlockVal THEN TRUE
                ELSE b.signature = Owner(b)

\* ----------------------------------------------------------------------
\* Ownership of private keys (for readability; not exported)
\* ----------------------------------------------------------------------
OwnedKey == [Node -> { pk \in PrivateKey : PubOf[pk] \in Account }]

\* Abstract mapping from private to public keys (must be provided in .cfg)
PubOf \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by .cfg)
\* ----------------------------------------------------------------------
\* THEOREM Spec => []SafetyInvariant

====