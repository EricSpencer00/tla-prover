---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (provided by the .cfg file)
CONSTANTS
    Hash,               \* Set of all possible block hashes
    NoHashVal,          \* Sentinel value meaning "no hash"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Natural number: total supply at genesis
    NoBlockVal,         \* Sentinel value meaning "no block"
    CalculateHash,      \* Abstract hash operator (overridden by the .cfg)
    PrivateToPublic,    \* [PrivateKey -> PublicKey]  (bijection)
    NodeOwnedKey        \* [Node -> PrivateKey]       (each node owns one private key)

\* ----------------------------------------------------------------------
\* The concrete implementation of the hash operator used for model checking.
\* The .cfg file substitutes CalculateHash with this operator.
CalculateHashImpl(b, ph) ==
    (* A simple nondeterministic choice of a hash value from the set Hash. *)
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Block type definition
Block ==
    [ blkType   : {"genesis", "send", "open", "receive", "change"},
      prevHash  : (Hash \cup {NoHashVal}),
      account   : PublicKey,
      amount    : Nat,
      dest      : PublicKey,
      rep       : PublicKey,
      srcHash   : (Hash \cup {NoHashVal}),
      sig       : PrivateKey ]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    LastHash,           \* The most recent block hash (or NoHashVal)
    Ledger,             \* Mapping from hashes to blocks (or NoBlockVal)
    Received            \* Mapping from each node to the set of blocks it has received but not yet processed

\* ----------------------------------------------------------------------
\* Helper definitions
NoHash == NoHashVal
NoBlock == NoBlockVal

BlockHash(b) == CalculateHashImpl(b, b.prevHash)

ValidSignature(b) == PrivateToPublic[b.sig] = b.account

\* Set of all blocks currently stored in the ledger
LedgerBlocks == { b \in Block : \E h \in Hash : Ledger[h] = b }

\* Compute the total balance of a given account by inspecting all its blocks
Balance(pub) ==
    LET
        accBlocks == { b \in LedgerBlocks : b.account = pub }
    IN
        IF accBlocks = {} THEN 0
        ELSE
            \* Sum of net amounts contributed by each block type
            Sum({ 
                CASE b.blkType = "genesis" -> b.amount
                     [] b.blkType = "receive" -> b.amount
                     [] b.blkType = "send"    -> -b.amount
                     [] OTHER                -> 0
                END
                : b \in accBlocks })

\* Simple recursive sum over a set of natural numbers
Sum(S) ==
    IF S = {} THEN 0
    ELSE
        LET e == CHOOSE x \in S : TRUE
        IN e + Sum(S \ {e})

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ LastHash = NoHashVal
    /\ Ledger = [h \in Hash |-> NoBlockVal]
    /\ Received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (may occur only once)
GenesisCreate ==
    /\ LastHash = NoHashVal                 \* no block has been created yet
    /\ \E n \in Node :
          LET pk == NodeOwnedKey[n] IN
          LET g == [ blkType  |-> "genesis",
                     prevHash |-> NoHashVal,
                     account  |-> PrivateToPublic[pk],
                     amount   |-> GenesisBalance,
                     dest     |-> NoHashVal,
                     rep      |-> NoHashVal,
                     srcHash  |-> NoHashVal,
                     sig      |-> pk ] IN
          /\ h == BlockHash(g)
          /\ LastHash' = h
          /\ Ledger'   = [Ledger EXCEPT ![h] = g]
          /\ Received' = [node \in Node |-> {}]   \* all nodes already have the block
          /\ UNCHANGED <<>>                     \* no other variables
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: a node creates a send block
SendCreate ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node :
          LET pk == NodeOwnedKey[n] IN
          LET senderPub == PrivateToPublic[pk] IN
          /\ \E amount \in Nat :
                /\ amount <= Balance(senderPub)               \* cannot overdraw
                LET s == [ blkType  |-> "send",
                           prevHash |-> LastHash,
                           account  |-> senderPub,
                           amount   |-> amount,
                           dest     |-> PrivateToPublic[pk],   \* placeholder destination
                           rep      |-> NoHashVal,
                           srcHash  |-> NoHashVal,
                           sig      |-> pk ] IN
                /\ h == BlockHash(s)
                /\ LastHash' = h
                /\ Ledger'   = [Ledger EXCEPT ![h] = s]
                /\ Received' = [node \in Node |-> Received[node] \cup {s}]
                /\ UNCHANGED <<>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: a node creates an open block (opens a new account)
OpenCreate ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node :
          LET pk == NodeOwnedKey[n] IN
          LET pub == PrivateToPublic[pk] IN
          /\ \E srcHash \in Hash :
                /\ Ledger[srcHash] # NoBlockVal
                /\ Ledger[srcHash].blkType = "send"
                /\ Ledger[srcHash].dest = pub          \* the send is addressed to this account
                LET o == [ blkType  |-> "open",
                           prevHash |-> NoHashVal,
                           account  |-> pub,
                           amount   |-> 0,
                           dest     |-> NoHashVal,
                           rep      |-> NoHashVal,
                           srcHash  |-> srcHash,
                           sig      |-> pk ] IN
                /\ h == BlockHash(o)
                /\ LastHash' = h
                /\ Ledger'   = [Ledger EXCEPT ![h] = o]
                /\ Received' = [node \in Node |-> Received[node] \cup {o}]
                /\ UNCHANGED <<>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: a node creates a receive block
ReceiveCreate ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node :
          LET pk == NodeOwnedKey[n] IN
          LET pub == PrivateToPublic[pk] IN
          /\ \E srcHash \in Hash :
                /\ Ledger[srcHash] # NoBlockVal
                /\ Ledger[srcHash].blkType = "send"
                /\ Ledger[srcHash].dest = pub
                /\ \E prevHash \in Hash :
                      /\ Ledger[prevHash] # NoBlockVal
                      /\ Ledger[prevHash].account = pub
                      LET amt == Ledger[srcHash].amount IN
                      LET r == [ blkType  |-> "receive",
                                 prevHash |-> prevHash,
                                 account  |-> pub,
                                 amount   |-> amt,
                                 dest     |-> NoHashVal,
                                 rep      |-> NoHashVal,
                                 srcHash  |-> srcHash,
                                 sig      |-> pk ] IN
                      /\ h == BlockHash(r)
                      /\ LastHash' = h
                      /\ Ledger'   = [Ledger EXCEPT ![h] = r]
                      /\ Received' = [node \in Node |-> Received[node] \cup {r}]
                      /\ UNCHANGED <<>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: a node creates a change representative block
ChangeCreate ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node :
          LET pk == NodeOwnedKey[n] IN
          LET pub == PrivateToPublic[pk] IN
          /\ \E newRep \in PublicKey :
                /\ \E prevHash \in Hash :
                      /\ Ledger[prevHash] # NoBlockVal
                      /\ Ledger[prevHash].account = pub
                      LET c == [ blkType  |-> "change",
                                 prevHash |-> prevHash,
                                 account  |-> pub,
                                 amount   |-> 0,
                                 dest     |-> NoHashVal,
                                 rep      |-> newRep,
                                 srcHash  |-> NoHashVal,
                                 sig      |-> pk ] IN
                      /\ h == BlockHash(c)
                      /\ LastHash' = h
                      /\ Ledger'   = [Ledger EXCEPT ![h] = c]
                      /\ Received' = [node \in Node |-> Received[node] \cup {c}]
                      /\ UNCHANGED <<>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: a node processes a received block (validates and records it)
ProcessBlock ==
    /\ \E n \in Node :
          /\ Received[n] # {}
          /\ \E b \in Received[n] :
                /\ ValidSignature(b)
                /\ (b.prevHash = NoHashVal \/ Ledger[b.prevHash] # NoBlockVal)
                /\ (b.blkType = "send" => b.amount <= Balance(b.account))
                LET h == BlockHash(b) IN
                /\ Ledger'   = [Ledger EXCEPT ![h] = b]
                /\ Received' = [Received EXCEPT ![n] = Received[n] \ {b}]
                /\ UNCHANGED <<LastHash>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ GenesisCreate
    \/ SendCreate
    \/ OpenCreate
    \/ ReceiveCreate
    \/ ChangeCreate
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ LastHash \in (Hash \cup {NoHashVal})
    /\ Ledger \in [Hash -> (Block \cup {NoBlockVal})]
    /\ Received \in [Node -> SUBSET Block]

\* ----------------------------------------------------------------------
\* Safety invariant: every block stored in any ledger has a valid signature
SafetyInvariant ==
    \A h \in Hash :
        IF Ledger[h] # NoBlockVal
        THEN ValidSignature(Ledger[h])
        ELSE TRUE
====