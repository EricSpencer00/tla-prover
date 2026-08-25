---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\*--------------------------- Constants ---------------------------

CONSTANTS
    Hash,            \* Set of all possible block hashes
    NoHashVal,       \* Sentinel value indicating no hash
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total supply of coins (a Nat)
    NoBlockVal,      \* Sentinel value indicating the absence of a block
    CalculateHash,   \* Abstract hash function (to be overridden)
    NoHash,          \* Alias for NoHashVal
    NoBlock          \* Alias for NoBlockVal

\*--------------------------- Derived constants ---------------------------

ASSUME
    /\ NoHash = NoHashVal
    /\ NoBlock = NoBlockVal

\* Mapping from a private key to its public key
CONSTANT Private2Public \* : PrivateKey -> PublicKey
\* Mapping from a node to the private key it owns
CONSTANT Node2Key      \* : Node -> PrivateKey
\* Mapping from a private key to an abstract signature (used for validation)
CONSTANT Signatures    \* : PrivateKey -> Sig

\*--------------------------- Types ---------------------------

Sig == UNION { Signatures[pk] : pk \in PrivateKey }

BlockType == {"genesis", "send", "receive", "open", "change"}

Block ==
    [ type       : BlockType,
      hash       : Hash,
      prev       : Hash,
      account    : PublicKey,
      recipient  : PublicKey,
      amount     : Nat,
      signature  : Sig,
      rep        : PublicKey ]

\*--------------------------- Variables ---------------------------

VARIABLES
    lastHash,   \* The most recent block hash (or NoHash)
    ledger,     \* Per‑node copy of the distributed ledger
    received    \* Per‑node set of block hashes awaiting validation

\* Ledger maps each node to a mapping from hash to either a Block or NoBlock
LedgerDomain == [h \in Hash |-> Block \/ NoBlock]

\*--------------------------- Helper functions ---------------------------

\* Retrieve the block with hash h from any node's ledger (there must be one if h is valid)
GetBlock(h) ==
    CHOOSE b \in UNION { ledger[n][h] : n \in Node } :
        b # NoBlock

\* Simple signature validation: the signature must correspond to the account's public key
ValidSignature(b) ==
    \E pk \in PrivateKey :
        /\ Private2Public[pk] = b.account
        /\ b.signature = Signatures[pk]

\* Placeholder predicates for type‑specific validation (kept abstract for this model)
ValidSend(b)     == TRUE
ValidOpen(b)     == TRUE
ValidReceive(b)  == TRUE
ValidChange(b)   == TRUE

\* Balance of an account is defined recursively by walking its chain.
\* For this abstract model we provide a very permissive definition.
Balance(pk) ==
    LET blocks == { b \in UNION { ledger[n][h] : n \in Node, h \in Hash } :
                     b # NoBlock /\ b.account = pk }
    IN
        IF pk = Private2Public[Node2Key[CHOOSE n \in Node : TRUE]]
        THEN GenesisBalance + (<<>> \* placeholder, always non‑negative *)
        ELSE 0

\*--------------------------- Initial state ---------------------------

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\*--------------------------- Actions ---------------------------

\* 1. Create the genesis block (only once)
GenesisCreate ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET pk == Private2Public[Node2Key[n]]
            h  == CHOOSE hh \in Hash : hh # NoHash
            b  == [ type       |-> "genesis",
                    hash       |-> h,
                    prev       |-> NoHash,
                    account    |-> pk,
                    recipient  |-> NoHash,
                    amount     |-> GenesisBalance,
                    signature  |-> Signatures[Node2Key[n]],
                    rep        |-> NoHash ]
        IN
            /\ lastHash' = h
            /\ \A m \in Node :
                ledger' = [ledger EXCEPT ![m] = [ledger[m] EXCEPT ![h] = b]]
            /\ received' = [received EXCEPT ![m] = {}]  \* broadcast, but pending sets start empty
    /\ UNCHANGED <<>>  \* all other variables unchanged (handled above)

\* 2. Create a send block
CreateSend ==
    /\ lastHash # NoHash
    /\ \E n \in Node :
        LET pk   == Private2Public[Node2Key[n]]
            amt  == 1                \* for simplicity we allow sending 1 unit
            hPrev == lastHash        \* reference the latest global hash (abstract)
            hNew  == CHOOSE hh \in Hash : hh # NoHash /\ hh # lastHash
            recPk == CHOOSE pk2 \in PublicKey : pk2 # pk   \* choose a different recipient
            b     == [ type       |-> "send",
                       hash       |-> hNew,
                       prev       |-> hPrev,
                       account    |-> pk,
                       recipient  |-> recPk,
                       amount     |-> amt,
                       signature  |-> Signatures[Node2Key[n]],
                       rep        |-> NoHash ]
        IN
            /\ VALID Send predicate
            /\ lastHash' = hNew
            /\ received' = [received EXCEPT ![m] = @ \cup {hNew} : m \in Node]
            /\ UNCHANGED ledger
    /\ UNCHANGED <<>>

\* 3. Create an open block (opening a new account)
CreateOpen ==
    /\ \E n \in Node :
        LET pk   == Private2Public[Node2Key[n]]
            hPrev == lastHash
            hNew  == CHOOSE hh \in Hash : hh # NoHash /\ hh # lastHash
            b     == [ type       |-> "open",
                       hash       |-> hNew,
                       prev       |-> NoHash,
                       account    |-> pk,
                       recipient  |-> NoHash,
                       amount     |-> 0,
                       signature  |-> Signatures[Node2Key[n]],
                       rep        |-> NoHash ]
        IN
            /\ lastHash' = hNew
            /\ received' = [received EXCEPT ![m] = @ \cup {hNew} : m \in Node]
            /\ UNCHANGED ledger
    /\ UNCHANGED <<>>

\* 4. Create a receive block
CreateReceive ==
    /\ \E n \in Node :
        LET pk   == Private2Public[Node2Key[n]]
            hPrev == lastHash
            hNew  == CHOOSE hh \in Hash : hh # NoHash /\ hh # lastHash
            b     == [ type       |-> "receive",
                       hash       |-> hNew,
                       prev       |-> hPrev,
                       account    |-> pk,
                       recipient  |-> NoHash,
                       amount     |-> 0,
                       signature  |-> Signatures[Node2Key[n]],
                       rep        |-> NoHash ]
        IN
            /\ lastHash' = hNew
            /\ received' = [received EXCEPT ![m] = @ \cup {hNew} : m \in Node]
            /\ UNCHANGED ledger
    /\ UNCHANGED <<>>

\* 5. Create a change representative block
CreateChange ==
    /\ \E n \in Node :
        LET pk   == Private2Public[Node2Key[n]]
            hPrev == lastHash
            hNew  == CHOOSE hh \in Hash : hh # NoHash /\ hh # lastHash
            newRep == CHOOSE pk2 \in PublicKey : pk2 # pk
            b     == [ type       |-> "change",
                       hash       |-> hNew,
                       prev       |-> hPrev,
                       account    |-> pk,
                       recipient  |-> NoHash,
                       amount     |-> 0,
                       signature  |-> Signatures[Node2Key[n]],
                       rep        |-> newRep ]
        IN
            /\ lastHash' = hNew
            /\ received' = [received EXCEPT ![m] = @ \cup {hNew} : m \in Node]
            /\ UNCHANGED ledger
    /\ UNCHANGED <<>>

\* 6. Process a received block at a node
ProcessReceived ==
    /\ \E n \in Node, h \in received[n] :
        LET b == GetBlock(h)
        IN
            /\ ValidSignature(b)
            /\ CASE b.type = "send"    -> ValidSend(b)
               [] b.type = "open"    -> ValidOpen(b)
               [] b.type = "receive"-> ValidReceive(b)
               [] b.type = "change" -> ValidChange(b)
               [] OTHER              -> TRUE
            /\ ledger' = [ledger EXCEPT ![n][h] = b]
            /\ received' = [received EXCEPT ![n] = @ \ {h}]
            /\ UNCHANGED <<lastHash>>

\* The overall next-state relation
Next ==
    \/ GenesisCreate
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\*--------------------------- Specification ---------------------------

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\*--------------------------- Invariants ---------------------------

TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \/ NoBlock)]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
                IF b = NoBlock THEN TRUE ELSE ValidSignature(b)

\*--------------------------- Substitution operator ---------------------------

\* This operator is intended to be overridden by the .cfg file.
CalculateHashImpl(d, p) == CalculateHash(d, p)

=============================================================================