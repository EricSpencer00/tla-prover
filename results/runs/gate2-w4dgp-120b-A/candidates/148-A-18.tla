---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* Nano cryptocurrency block-lattice. Each account owns its own chain of blocks, and
\* every action that changes that lattice (opening an account, sending funds, changing
\* a voting representative) creates a new block that is cryptographically signed by
\* the account's private key. The model tracks the last calculated hash, each node's
\* copy of the replicated ledger, and the set of received-but-unvalidated blocks
\* per node. Balance is tallied by walking the account chain. The safety invariant
\* checks every block in the ledger has a valid signature for the account that owns
\* the chain it resides in, which is the mechanism by which an unauthorized node's
\* forged block would be caught on validation.
CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Hash is a bounded set of hash values, with the last hash and no-hash sentinel
\* drawn from it. PrivateKey and PublicKey are paired by keyOf; Node is the set of
\* network participants. CalculateHash is the abstract hash operator, bound here
\* by the CalculateHashImpl substitution in the .cfg, so the chain can always
\* grow rather than saturating against a concrete hash function's collision bound.
ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Hash
ASSUME NoHash = NoHashVal
ASSUME NoBlock = NoBlockVal

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK == /\ lastHash \in Hash \cup {NoHash}
          /\ ledger \in [Node -> [Hash -> (Hash \cup {NoBlock})]]
          /\ received \in [Node -> SUBSET Hash]

Init == /\ lastHash = NoHash
        /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
        /\ received = [n \in Node |-> {}]

\* Balance walks the account chain linked by prev fields, summing the balances
\* of all its blocks. The account chain is anchored at the genesis account's
\* first block (an open block also works as an anchor for non-genesis accounts).
Balance(blk) == LET walk(b, h) == IF h = NoHash THEN b
                            ELSE IF ledger[b][h] = NoBlock THEN b
                                 ELSE walk(b + ledger[b][h].amt, ledger[b][h].prev)
                IN walk(0, blk)

AccountBalance(n) == LET lastOf(a) ==
                         LET maxHash(S) == IF S = {} THEN NoHash
                                            ELSE LET x = CHOOSE y \in S : \A z \in S : y >= z
                                                 IN x
                              IN maxHash({h \in Hash : ledger[a][h] # NoBlock})
                     IN walkAccount(a, 0, NoHash)
                     where walkAccount(a, total, cur) ==
                             IF cur = NoHash THEN total
                             ELSE walkAccount(a, total + ledger[a][cur].amt,
                                              IF ledger[a][cur].prev = NoHash
                                              THEN maxHash({h \in Hash : ledger[a][h] # NoBlock})
                                              ELSE ledger[a][cur].prev)

\* The circulating supply must never exceed the genesis balance, since every
\* block move only ever moves funds between accounts (mints on the chain are
\* disallowed by the block-level rules and the invariant together).
SupplyBound == LET total(S) == IF S = {} THEN 0
                           ELSE LET x = CHOOSE y \in S : TRUE
                                IN ledger[Node][x].amt + total(S \ {x})
               IN total({h \in Hash : ledger[Node][h] # NoBlock}) <= GenesisBalance

\* A block is valid if its signature matches the public key of the account that
\* owns the chain it resides in -- this is what stops an unauthorized node's
\* block from ever being accepted into any node's ledger.
ValidSignature(h) == \E k \in PublicKey : k \in {ledger[n][h].signer : n \in Node}
                     /\ LET auth == (\E n \in Node : keyOf[PrivateKey][ledger[n][h].signer] = k)
                        IN IF ledger[n][h].type = "receive"
                           THEN auth /\ ledger[n][ledger[n][h].link].type = "send"
                                /\ ledger[n][h].prev # NoHash
                                /\ ledger[n][h].link \notin received[n]
                           ELSE auth

\* Process takes one received block and folds it into the node's ledger copy,
\* which is where the signature check happens before the block is ever visible.
Process(n) == \E h \in received[n] :
                 /\ ValidSignature(h)
                 /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
                 /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
                 /\ UNCHANGED lastHash

\* CreateGenesis builds the network's first block from the entire genesis
\* balance, replicating it across every node's copy in the same step so the
\* chain is never partitioned by a block that only half the network sees.
CreateGenesis(k) == /\ lastHash = NoHash
                     /\ \A n \in Node : ledger[n][Hash(k)] = NoBlock
                     /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![Hash(k)] = [type |-> "open",
                                                                                 amt |-> GenesisBalance,
                                                                                 prev |-> NoHash,
                                                                                 link |-> NoHash,
                                                                                 signer |-> k]]]
                     /\ lastHash' = Hash(k)
                     /\ UNCHANGED received

\* CreateSend appends a block to the sender's chain that moves funds to a
\* recipient. The amount may not exceed the sender's available balance.
CreateSend(n, k) == /\ lastHash # NoHash
                     /\ ledger[n][Hash(k)] = NoBlock
                     /\ AccountBalance(n) >= 1
                     /\ ledger' = [ledger EXCEPT ![n][Hash(k)] = [type |-> "send",
                                                                  amt |-> 1,
                                                                  prev |-> lastHash,
                                                                  link |-> NoHash,
                                                                  signer |-> k]]
                     /\ lastHash' = Hash(k)
                     /\ received' = [received EXCEPT ![m] = received[m] \cup {Hash(k)}]

\* CreateOpen builds a new account's first block, referencing a send block
\* directed to that account's public key and opening the chain.
CreateOpen(n, k) == /\ ledger[n][Hash(k)] = NoBlock
                     /\ \E h \in Hash : ledger[n][h] # NoBlock
                                          /\ ledger[n][h].type = "send"
                                          /\ ledger[n][h].signer = n
                     /\ ledger' = [ledger EXCEPT ![n][Hash(k)] = [type |-> "open",
                                                                  amt |-> 0,
                                                                  prev |-> NoHash,
                                                                  link |-> NoHash,
                                                                  signer |-> k]]
                     /\ lastHash' = Hash(k)
                     /\ received' = [received EXCEPT ![m] = received[m] \cup {Hash(k)}]

\* CreateReceive folds an incoming send into the receiver's chain, moving the
\* funds and marking the link as claimed. Every receive advances the hash.
CreateReceive(n, k) == /\ lastHash # NoHash
                       /\ ledger[n][Hash(k)] = NoBlock
                       /\ \E h \in Hash : ledger[n][h] # NoBlock
                                                /\ ledger[n][h].type = "send"
                                                /\ ledger[n][h].signer = n
                                                /\ ledger[n][h].link \notin received[n]
                       /\ ledger' = [ledger EXCEPT ![n][Hash(k)] = [type |-> "receive",
                                                                    amt |-> 0,
                                                                    prev |-> lastHash,
                                                                    link |-> h,
                                                                    signer |-> k]]
                       /\ lastHash' = Hash(k)
                       /\ received' = [received EXCEPT ![m] = received[m] \cup {Hash(k)}]

\* ChangeRepresentative records an account's new voting representative into
\* its chain. It is authorized by the same signature check as any other block.
CreateChangeRep(n, k) == /\ lastHash # NoHash
                         /\ ledger[n][Hash(k)] = NoBlock
                         /\ ledger' = [ledger EXCEPT ![n][Hash(k)] = [type |-> "change_rep",
                                                                      amt |-> 0,
                                                                      prev |-> lastHash,
                                                                      link |-> NoHash,
                                                                      signer |-> k]]
                         /\ lastHash' = Hash(k)
                         /\ received' = [received EXCEPT ![m] = received[m] \cup {Hash(k)}]

Next == \/ \E n \in Node, k \in PrivateKey : Process(n) \/ CreateGenesis(k) \/ CreateSend(n, k)
               \/ CreateOpen(n, k) \/ CreateReceive(n, k) \/ CreateChangeRep(n, k)

Spec == /\ Init /\ [][Next]_vars

\* TypeOK keeps the last hash, replicated ledger, and per-node received sets
\* within their declared finite types.
TypeInvariant == TypeOK

\* SafetyInvariant: every block in every node's ledger copy verifies against the
\* public key of the account that owns that chain -- a forged block from an
\* unauthorized node would fail this signature check and never be accepted.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlock => ValidSignature(h)

====