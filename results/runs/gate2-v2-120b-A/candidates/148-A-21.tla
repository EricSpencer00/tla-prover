---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (as required by the .cfg)
-----------------------------------------------------------------*)
CONSTANTS 
    Hash,               \* the set of all possible block hashes
    NoHashVal,          \* a distinguished sentinel hash meaning "no hash yet"
    PrivateKey,         \* the set of all private keys
    PublicKey,          \* the set of all public keys
    Node,               \* the set of all network nodes
    GenesisBalance,     \* the total amount of coins at genesis (a Nat)
    NoBlockVal,         \* a distinguished sentinel meaning "no block"
    CalculateHash,      \* abstract hash function: [data, prevHash -> Hash]
    NoHash,             \* alias for NoHashVal (for readability)
    NoBlock             \* alias for NoBlockVal (for readability)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Accounts == PublicKey

(*-----------------------------------------------------------------
  Block types
-----------------------------------------------------------------*)
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

(*-----------------------------------------------------------------
  Payload record (a generic description of block contents)
-----------------------------------------------------------------*)
Block == [type          : BlockType,
          prev          : Hash,
          source        : PublicKey,   \* for Send, Open, Receive, Change
          destination   : PublicKey,   \* for Send, Open, Receive (or NoPublicKey)
          amount        : Nat,
          signer        : PublicKey,   \* the account that signs this block
          signature     : Nat]          \* abstract signature (a Nat)

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES 
    lastHash,               \* the hash of the most recent block globally
    ledger,                 \* [node -> [hash -> Block]]
    received                \* [node -> SUBSET Hash]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* The set of all block hashes that are currently used (or the sentinel)
AllHashes == { NoHashVal } \cup { h \in Hash : \E n \in Node : h \in DOMAIN ledger[n] }

\* Retrieve the block for a given node and hash (or NoBlock sentinel)
BlockAt(node, h) == 
    IF h = NoHashVal THEN NoBlockVal 
    ELSE ledger[node][h]

\* Validate a signature (abstractly, just equality of a hash of the data)
SignatureValid(sig, data, pk) == 
    sig = 0  \* placeholder: all signatures are considered valid in this abstract model

\* Compute the balance of an account on a given node by walking its chain
\* This is a recursive function defined using a set of visited hashes to avoid loops
Balance(node, acct) == 
    LET Walk(hs, visited) == 
        IF hs = {} THEN 0
        ELSE 
            LET h == CHOOSE x \in hs : TRUE IN
            LET blk == BlockAt(node, h) IN
            IF blk = NoBlockVal THEN 0
            ELSE 
                LET rest == hs \ {h} IN
                IF blk.type = "Send" THEN 
                    IF blk.signer = acct THEN -blk.amount + Walk(rest, visited \cup {h})
                    ELSE Walk(rest, visited \cup {h})
                ELSE IF blk.type = "Receive" THEN 
                    IF blk.signer = acct THEN blk.amount + Walk(rest, visited \cup {h})
                    ELSE Walk(rest, visited \cup {h})
                ELSE IF blk.type = "Open" THEN 
                    IF blk.signer = acct THEN blk.amount + Walk(rest, visited \cup {h})
                    ELSE Walk(rest, visited \cup {h})
                ELSE IF blk.type = "Change" THEN 
                    Walk(rest, visited \cup {h})
                ELSE IF blk.type = "Genesis" THEN 
                    IF blk.signer = acct THEN blk.amount + Walk(rest, visited \cup {h})
                    ELSE Walk(rest, visited \cup {h})
                ELSE Walk(rest, visited \cup {h})
    IN Walk({h \in DOMAIN ledger[node] : 
                ledger[node][h].signer = acct}, {})

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in {} |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

(*-----------------------------------------------------------------
  Action definitions
-----------------------------------------------------------------*)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E creator \in Node, pk \in PublicKey, sk \in PrivateKey :
        /\ creator \in Node
        /\ (sk, pk) \in { <<sk, pk>> : sk \in PrivateKey, pk \in PublicKey }  \* abstract keypair relation
        /\ blk == [type          |-> "Genesis",
                  prev          |-> NoHashVal,
                  source        |-> pk,
                  destination   |-> pk,
                  amount        |-> GenesisBalance,
                  signer        |-> pk,
                  signature     |-> 0]
        /\ newHash == CalculateHash(blk, NoHashVal)
        /\ ledger' = [n \in Node |-> 
                        [h \in ledger[n] : ledger[n][h]] @@ 
                        [newHash |-> blk]]
        /\ lastHash' = newHash
        /\ received' = [n \in Node |-> {}]
    /\ UNCHANGED << >>

CreateSend ==
    /\ lastHash # NoHashVal
    /\ \E senderNode \in Node, senderPk \in PublicKey, senderSk \in PrivateKey,
          recvPk \in PublicKey, amt \in Nat :
        /\ (senderSk, senderPk) \in { <<sk, pk>> : sk \in PrivateKey, pk \in PublicKey }
        /\ Balance(senderNode, senderPk) >= amt
        /\ blk == [type          |-> "Send",
                  prev          |-> lastHash,
                  source        |-> senderPk,
                  destination   |-> recvPk,
                  amount        |-> amt,
                  signer        |-> senderPk,
                  signature     |-> 0]
        /\ newHash == CalculateHash(blk, lastHash)
        /\ ledger' = [n \in Node |-> 
                        ledger[n] @@ [newHash |-> blk]]
        /\ lastHash' = newHash
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
    /\ UNCHANGED << >>

CreateOpen ==
    /\ lastHash # NoHashVal
    /\ \E openerNode \in Node, openerPk \in PublicKey, openerSk \in PrivateKey,
          sendHash \in Hash :
        /\ (openerSk, openerPk) \in { <<sk, pk>> : sk \in PrivateKey, pk \in PublicKey }
        /\ sendHash \in DOMAIN ledger[openerNode]
        /\ BlockAt(openerNode, sendHash).type = "Send"
        /\ BlockAt(openerNode, sendHash).destination = openerPk
        /\ blk == [type          |-> "Open",
                  prev          |-> NoHashVal,
                  source        |-> openerPk,
                  destination   |-> openerPk,
                  amount        |-> BlockAt(openerNode, sendHash).amount,
                  signer        |-> openerPk,
                  signature     |-> 0]
        /\ newHash == CalculateHash(blk, NoHashVal)
        /\ ledger' = [n \in Node |-> ledger[n] @@ [newHash |-> blk]]
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
        /\ lastHash' = newHash
    /\ UNCHANGED << >>

CreateReceive ==
    /\ lastHash # NoHashVal
    /\ \E receiverNode \in Node, receiverPk \in PublicKey, receiverSk \in PrivateKey,
          sendHash \in Hash :
        /\ (receiverSk, receiverPk) \in { <<sk, pk>> : sk \in PrivateKey, pk \in PublicKey }
        /\ sendHash \in DOMAIN ledger[receiverNode]
        /\ BlockAt(receiverNode, sendHash).type = "Send"
        /\ BlockAt(receiverNode, sendHash).destination = receiverPk
        /\ blk == [type          |-> "Receive",
                  prev          |-> lastHash,
                  source        |-> receiverPk,
                  destination   |-> receiverPk,
                  amount        |-> BlockAt(receiverNode, sendHash).amount,
                  signer        |-> receiverPk,
                  signature     |-> 0]
        /\ newHash == CalculateHash(blk, lastHash)
        /\ ledger' = [n \in Node |-> ledger[n] @@ [newHash |-> blk]]
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
        /\ lastHash' = newHash
    /\ UNCHANGED << >>

CreateChange ==
    /\ lastHash # NoHashVal
    /\ \E changerNode \in Node, changerPk \in PublicKey, changerSk \in PrivateKey :
        /\ (changerSk, changerPk) \in { <<sk, pk>> : sk \in PrivateKey, pk \in PublicKey }
        /\ blk == [type          |-> "Change",
                  prev          |-> lastHash,
                  source        |-> changerPk,
                  destination   |-> changerPk,
                  amount        |-> 0,
                  signer        |-> changerPk,
                  signature     |-> 0]
        /\ newHash == CalculateHash(blk, lastHash)
        /\ ledger' = [n \in Node |-> ledger[n] @@ [newHash |-> blk]]
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
        /\ lastHash' = newHash
    /\ UNCHANGED << >>

ProcessBlock(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET blk == BlockAt(node, h) IN
        /\ blk # NoBlockVal
        /\ blk.signature = 0                      \* abstract signature check
        /\ ledger' = [n \in Node |-> 
                        IF n = node THEN ledger[n] @@ [h |-> blk] ELSE ledger[n]]
        /\ received' = [n \in Node |-> IF n = node THEN received[n] \ {h} ELSE received[n]]
    /\ UNCHANGED << lastHash >>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
      \A h \in DOMAIN ledger[n] :
        LET blk == ledger[n][h] IN
        /\ blk.type \in BlockType
        /\ blk.signer \in PublicKey
        /\ blk.signature = 0               \* abstract signature validity
        /\ 
           (* Basic structural checks per block type *)
           IF blk.type = "Genesis" THEN
               blk.amount = GenesisBalance
           ELSE IF blk.type = "Send" THEN
               blk.amount <= Balance(n, blk.signer)
           ELSE IF blk.type \in {"Open", "Receive", "Change"} THEN
               TRUE
           ELSE FALSE

=============================================================================