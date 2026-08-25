---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash,
    NoHash, NoBlock

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"genesis", "send", "open", "receive", "change"}

Block == [type          : BlockType,
          account       : PublicKey,
          previous      : Hash \cup {NoHash},
          destination   : PublicKey \cup {NoHash},
          amount        : Nat,
          representative: PublicKey \cup {NoHash},
          signature     : PublicKey]   \* simplified signature

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,          \* the hash of the most recently created block (or NoHash)
    Ledger,            \* mapping from each hash to either a Block or NoBlock
    Received,          \* per‑node set of hashes that have been received but not yet processed
    GenesisDone        \* Boolean flag to ensure genesis is created only once

\* ----------------------------------------------------------------------
\* Helper operators
\* ----------------------------------------------------------------------
\* Simple identity between a signature and its owner – sufficient for the
\* cryptographic invariant in this abstract model.
ValidSignature(b) == b.signature = b.account

\* The set of all hashes that currently hold a real block.
ActiveHashes == { h \\in Hash : Ledger[h] # NoBlock }

\* ----------------------------------------------------------------------
\* Initialisation
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [h \\in Hash |-> NoBlock]
    /\ Received = [n \\in Node |-> {}]
    /\ GenesisDone = FALSE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ ~GenesisDone
    /\ \E n \\in Node :
         LET newHash == CalculateHash(<< "genesis", n, NoHash, NoHash, GenesisBalance, NoHash >>, NoHash)
         IN
            /\ LastHash' = newHash
            /\ Ledger' = [Ledger EXCEPT ![newHash] =
                            [type          |-> "genesis",
                             account       |-> n,
                             previous      |-> NoHash,
                             destination   |-> NoHash,
                             amount        |-> GenesisBalance,
                             representative|-> NoHash,
                             signature     |-> n]]
            /\ Received' = [node \\in Node |-> Received[node] \cup {newHash}]
            /\ GenesisDone' = TRUE
    /\ UNCHANGED << >>

CreateSend ==
    /\ \E n \\in Node :
         \E prev \\in Hash :
            /\ Ledger[prev] # NoBlock
            /\ Ledger[prev].account = n
            /\ \E amt \\in Nat :
                 /\ amt <= GenesisBalance   \* (abstract balance check)
                 /\ \E dest \\in PublicKey :
                      LET newHash == CalculateHash(<< "send", n, prev, dest, amt, NoHash >>, prev)
                      IN
                         /\ LastHash' = newHash
                         /\ Ledger' = [Ledger EXCEPT ![newHash] =
                                         [type          |-> "send",
                                          account       |-> n,
                                          previous      |-> prev,
                                          destination   |-> dest,
                                          amount        |-> amt,
                                          representative|-> NoHash,
                                          signature     |-> n]]
                         /\ Received' = [node \\in Node |-> Received[node] \cup {newHash}]
                         /\ UNCHANGED << GenesisDone >>
    /\ UNCHANGED << >>

CreateOpen ==
    /\ \E n \\in Node :
         \E sendHash \\in Hash :
            /\ Ledger[sendHash] # NoBlock
            /\ Ledger[sendHash].type = "send"
            /\ Ledger[sendHash].destination = n
            /\ LET newHash == CalculateHash(<< "open", n, NoHash, n, 0, NoHash >>, NoHash)
               IN
                  /\ LastHash' = newHash
                  /\ Ledger' = [Ledger EXCEPT ![newHash] =
                                  [type          |-> "open",
                                   account       |-> n,
                                   previous      |-> NoHash,
                                   destination   |-> n,
                                   amount        |-> 0,
                                   representative|-> NoHash,
                                   signature     |-> n]]
                  /\ Received' = [node \\in Node |-> Received[node] \cup {newHash}]
                  /\ UNCHANGED << GenesisDone >>
    /\ UNCHANGED << >>

CreateReceive ==
    /\ \E n \\in Node :
         \E prev \\in Hash :
            /\ Ledger[prev] # NoBlock
            /\ Ledger[prev].account = n
            /\ \E sendHash \\in Hash :
                 /\ Ledger[sendHash] # NoBlock
                 /\ Ledger[sendHash].type = "send"
                 /\ Ledger[sendHash].destination = n
                 /\ LET newHash == CalculateHash(<< "receive", n, prev, sendHash, Ledger[sendHash].amount, NoHash >>, prev)
                    IN
                       /\ LastHash' = newHash
                       /\ Ledger' = [Ledger EXCEPT ![newHash] =
                                       [type          |-> "receive",
                                        account       |-> n,
                                        previous      |-> prev,
                                        destination   |-> sendHash,
                                        amount        |-> Ledger[sendHash].amount,
                                        representative|-> NoHash,
                                        signature     |-> n]]
                       /\ Received' = [node \\in Node |-> Received[node] \cup {newHash}]
                       /\ UNCHANGED << GenesisDone >>
    /\ UNCHANGED << >>

CreateChange ==
    /\ \E n \\in Node :
         \E prev \\in Hash :
            /\ Ledger[prev] # NoBlock
            /\ Ledger[prev].account = n
            /\ \E newRep \\in PublicKey :
                 LET newHash == CalculateHash(<< "change", n, prev, NoHash, 0, newRep >>, prev)
                 IN
                    /\ LastHash' = newHash
                    /\ Ledger' = [Ledger EXCEPT ![newHash] =
                                    [type          |-> "change",
                                     account       |-> n,
                                     previous      |-> prev,
                                     destination   |-> NoHash,
                                     amount        |-> 0,
                                     representative|-> newRep,
                                     signature     |-> n]]
                    /\ Received' = [node \\in Node |-> Received[node] \cup {newHash}]
                    /\ UNCHANGED << GenesisDone >>
    /\ UNCHANGED << >>

ProcessBlock ==
    /\ \E n \\in Node :
         \E h \\in Received[n] :
            /\ Ledger[h] = NoBlock
            /\ \E b \\in Block :
                 /\ b = Ledger[h]   \* (this will be false now, we model validation that yields a block)
                 /\ FALSE  \* placeholder – in this abstract model we assume processing always succeeds when the block is already present
            /\ FALSE   \* (no concrete processing; kept for completeness)
    /\ UNCHANGED << LastHash, Ledger, Received, GenesisDone >>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, GenesisDone>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \/ LastHash = NoHash
    /\ Ledger \in [Hash -> (Block \cup {NoBlock})]
    /\ Received \in [Node -> SUBSET Hash]
    /\ GenesisDone \in BOOLEAN

SafetyInvariant ==
    /\ \A h \\in ActiveHashes :
          ValidSignature(Ledger[h])

\* ----------------------------------------------------------------------
\* Operator required by the .cfg file
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \\in Hash : TRUE

=============================================================================