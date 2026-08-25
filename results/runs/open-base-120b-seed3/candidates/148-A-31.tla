---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* --------------------------------------------------------------
\* CONSTANTS (provided by the .cfg file)
\* --------------------------------------------------------------
CONSTANTS
    Hash,                \* The set of all possible block hashes
    NoHashVal,           \* Sentinel value meaning “no hash”
    PrivateKey,          \* Set of private keys
    PublicKey,           \* Set of public keys
    Node,                \* Set of network nodes
    GenesisBalance,      \* Natural number – total supply at genesis
    NoBlockVal,          \* Sentinel value meaning “no block”
    CalculateHash,       \* Abstract hash operator (will be overridden)
    NoHash,              \* Alias for the sentinel hash
    NoBlock              \* Alias for the sentinel block

\* Aliases for readability
NoHash == NoHashVal
NoBlock == NoBlockVal

\* --------------------------------------------------------------
\* DERIVED CONSTANTS / HELPERS
\* --------------------------------------------------------------
\* Mapping from a private key to its public key (abstract, can be
\* instantiated by the configuration if needed)
CONSTANT PrivToPub \in [PrivateKey -> PublicKey]

\* --------------------------------------------------------------
\* BLOCK DEFINITION
\* --------------------------------------------------------------
Block ==
    [ hash    : Hash,
      type    : {"genesis","send","open","receive","change"},
      prev    : Hash,
      account : PublicKey,
      dest    : PublicKey,
      amount  : Nat,
      sig     : PublicKey ]

\* The empty sentinel block used for uninitialised entries
EmptyBlock == NoBlock

\* --------------------------------------------------------------
\* STATE VARIABLES
\* --------------------------------------------------------------
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHash)
    ledger,     \* Ledger[node][hash] = Block or NoBlock
    received    \* received[node] = set of blocks pending validation

\* --------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]

\* --------------------------------------------------------------
\* CRYPTOGRAPHIC HELPERS
\* --------------------------------------------------------------
\* A block is considered correctly signed when its signature equals
\* the public key of the account that owns the chain.
ValidSignature(b) == b.sig = b.account

\* --------------------------------------------------------------
\* BALANCE / REFERENCE HELPERS (simplified)
\* --------------------------------------------------------------
\* For the purpose of this specification we do not compute balances
\* precisely; the required safety property only concerns signatures.
\* The following placeholder predicates are provided for completeness.

\* The previous block referenced by b must already exist in the ledger
PrevExists(b, n) ==
    b.prev = NoHash \/ ledger[n][b.prev] # NoBlock

\* A send block cannot create money out of thin air – this is an
\* abstract check that the amount is non‑negative.
ValidAmount(b) == b.amount \in Nat

\* --------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------

\* -----------------------------------------------------------------
\* CreateGenesis – can fire only once, when lastHash = NoHash
\* -----------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash
    \* Choose a node that will own the genesis private key
    /\ \E n \in Node :
         \E pk \in PrivateKey :
            LET pub  == PrivToPub[pk] IN
            LET b   == [ hash    |-> newHash,
                         type    |-> "genesis",
                         prev    |-> NoHash,
                         account |-> pub,
                         dest    |-> pub,
                         amount  |-> GenesisBalance,
                         sig     |-> pub ] IN
            LET newHash == CalculateHashImpl(b, NoHash) IN
            /\ newHash \in Hash
            /\ lastHash' = newHash
            /\ ledger' = [ m \in Node |-> ledger[m] @@ [newHash |-> b] ]
            /\ received' = [ m \in Node |-> {} ]
            /\ UNCHANGED << >>   \* No other variables
    /\ UNCHANGED << >>   \* dummy to satisfy syntax

\* -----------------------------------------------------------------
\* CreateSend – a node creates a send block and broadcasts it
\* -----------------------------------------------------------------
CreateSend ==
    /\ \E n \in Node :
         \E pk \in PrivateKey :
            LET pub == PrivToPub[pk] IN
            \E prevHash \in Hash :
               /\ ledger[n][prevHash] # NoBlock
               /\ ledger[n][prevHash].account = pub
               /\ \E amt \in Nat :
                      /\ amt \le GenesisBalance   \* abstract balance check
                      LET b == [ hash    |-> newHash,
                                 type    |-> "send",
                                 prev    |-> prevHash,
                                 account |-> pub,
                                 dest    |-> destPub,
                                 amount  |-> amt,
                                 sig     |-> pub ] IN
                      LET destPub == ChoosePublicKey EXCEPT destPub # pub IN
                      LET newHash == CalculateHashImpl(b, prevHash) IN
                      /\ newHash \in Hash
                      /\ lastHash' = newHash
                      /\ ledger' = ledger
                      /\ received' = [ m \in Node |-> received[m] \cup {b} ]
                      /\ UNCHANGED << >> 
    /\ UNCHANGED << >> 

\* -----------------------------------------------------------------
\* CreateOpen – a node opens a new account referencing a send block
\* -----------------------------------------------------------------
CreateOpen ==
    /\ \E n \in Node :
         \E sendBlk \in received[n] :
            /\ sendBlk.type = "send"
            /\ sendBlk.dest = myPub
            /\ \E pk \in PrivateKey :
                 LET myPub == PrivToPub[pk] IN
                 LET b == [ hash    |-> newHash,
                            type    |-> "open",
                            prev    |-> NoHash,
                            account |-> myPub,
                            dest    |-> myPub,
                            amount  |-> sendBlk.amount,
                            sig     |-> myPub ] IN
                 LET newHash == CalculateHashImpl(b, NoHash) IN
                 /\ newHash \in Hash
                 /\ lastHash' = newHash
                 /\ ledger' = ledger
                 /\ received' = [ m \in Node |-> received[m] \cup {b} ]
                 /\ UNCHANGED << >>
    /\ UNCHANGED << >>

\* -----------------------------------------------------------------
\* CreateReceive – a node receives a previously sent amount
\* -----------------------------------------------------------------
CreateReceive ==
    /\ \E n \in Node :
         \E recvPrev \in Hash :
            /\ ledger[n][recvPrev] # NoBlock
            /\ \E sendBlk \in received[n] :
               /\ sendBlk.type = "send"
               /\ sendBlk.dest = myPub
               /\ \E pk \in PrivateKey :
                    LET myPub == PrivToPub[pk] IN
                    LET b == [ hash    |-> newHash,
                               type    |-> "receive",
                               prev    |-> recvPrev,
                               account |-> myPub,
                               dest    |-> myPub,
                               amount  |-> sendBlk.amount,
                               sig     |-> myPub ] IN
                    LET newHash == CalculateHashImpl(b, recvPrev) IN
                    /\ newHash \in Hash
                    /\ lastHash' = newHash
                    /\ ledger' = ledger
                    /\ received' = [ m \in Node |-> received[m] \cup {b} ]
                    /\ UNCHANGED << >>
    /\ UNCHANGED << >>

\* -----------------------------------------------------------------
\* CreateChange – a node changes its voting representative
\* -----------------------------------------------------------------
CreateChange ==
    /\ \E n \in Node :
         \E pk \in PrivateKey :
            LET pub == PrivToPub[pk] IN
            \E prevHash \in Hash :
               /\ ledger[n][prevHash] # NoBlock
               /\ ledger[n][prevHash].account = pub
               LET b == [ hash    |-> newHash,
                          type    |-> "change",
                          prev    |-> prevHash,
                          account |-> pub,
                          dest    |-> pub,
                          amount  |-> 0,
                          sig     |-> pub ] IN
               LET newHash == CalculateHashImpl(b, prevHash) IN
               /\ newHash \in Hash
               /\ lastHash' = newHash
               /\ ledger' = ledger
               /\ received' = [ m \in Node |-> received[m] \cup {b} ]
               /\ UNCHANGED << >>
    /\ UNCHANGED << >>

\* -----------------------------------------------------------------
\* ProcessBlock – a node validates and installs a received block
\* -----------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node :
         \E b \in received[n] :
            /\ ValidSignature(b)
            /\ PrevExists(b, n)
            /\ \* type‑specific abstract checks
               IF b.type = "send" THEN ValidAmount(b)
               ELSE IF b.type = "receive" THEN ValidAmount(b)
               ELSE IF b.type = "open"    THEN ValidAmount(b)
               ELSE IF b.type = "change" THEN TRUE
               ELSE TRUE
            LET h == b.hash IN
            /\ ledger' = [ m \in Node |
                          IF m = n
                          THEN ledger[m] @@ [h |-> b]
                          ELSE ledger[m] ]
            /\ received' = [ m \in Node |
                              IF m = n
                              THEN received[m] \ {b}
                              ELSE received[m] ]
            /\ UNCHANGED lastHash

\* -----------------------------------------------------------------
\* NEXT – nondeterministic choice of any enabled action
\* -----------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* --------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* --------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Block]

SafetyInvariant ==
    /\ \A n \in Node :
         \A h \in Hash :
            IF ledger[n][h] # NoBlock
            THEN ledger[n][h].sig = ledger[n][h].account
            ELSE TRUE

\* --------------------------------------------------------------
\* CALCULATE HASH IMPLEMENTATION (finite version for model checking)
\* --------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

====