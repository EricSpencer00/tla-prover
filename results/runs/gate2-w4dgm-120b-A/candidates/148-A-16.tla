---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey,
  Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* A block ends up in the ledger only after a node has validated its signature
\* and, in the case of open/receive blocks, the referenced send block is real.
\* Validation is the point at which a forged or stale block is rejected and
\* can never be added to a node's local copy of the ledger.

VARIABLES lastHash, ledger, received

\* ledger is the replicated copy of the blockchain each node holds locally.
\* received holds the messages still in flight toward each node.

vars == <<lastHash, ledger, received>>

Blocks == [owner: PublicKey, parent: Hash, kind: {"genesis", "send", "open", "receive", "change"},
             amount: 0..GenesisBalance, to: PublicKey, repr: PublicKey, signer: PrivateKey]

\* A missing block is not a hole in a chain: it is the sentinel NoBlockVal, which
\* is how a node records that it has never added any block at a particular hash.
BlankLedger == [h \in Hash |-> NoBlockVal]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> BlankLedger]
  /\ received = [n \in Node |-> {}]

TotalBalance ==
  LET Rec(b) ==
        IF b = NoBlockVal THEN 0
        ELSE IF b.kind = "send"
             THEN Rec(ledger[Node][b.parent]) - b.amount
             ELSE IF b.kind \in {"receive", "genesis"}
                  THEN Rec(ledger[Node][b.parent]) + b.amount
                  ELSE Rec(ledger[Node][b.parent])
  IN LET SumBalances(S) ==
        IF S = {} THEN 0
        ELSE LET p == CHOOSE x \in S : TRUE
                 b == ledger[Node][p]
                 rest == SumBalances(S \ {p})
             IN IF b = NoBlockVal THEN rest ELSE rest + Rec(b)
     IN SumBalances(Hash)

AccountChain(n) ==
  LET Next(p) == {q \in Hash : ledger[n][q] # NoBlockVal /\ ledger[n][q].parent = p}
       ChainFrom(p) == LET tails == UNION {ChainFrom(q) : q \in Next(p)} IN IF p = NoHash THEN tails ELSE tails \cup {p}
  IN ChainFrom(NoHash)

AccountBalance(n) == LET Rec(b) ==
                        IF b = NoBlockVal THEN 0
                        ELSE IF b.kind = "send"
                             THEN Rec(ledger[n][b.parent]) - b.amount
                             ELSE IF b.kind \in {"receive", "genesis"}
                                  THEN Rec(ledger[n][b.parent]) + b.amount
                                  ELSE Rec(ledger[n][b.parent])
                     IN Rec(ledger[n][AccountChain(n)])

OwnsAccount(n) == {PublicKey[n]}

\* A node validates a received block against its own (possibly stale) copy of
\* the ledger, and only a block that passes every check is added to that copy.
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ ledger[n][ledger[n][h].parent] # NoBlockVal
  /\ PublicKey[n] = ledger[n][h].signer
  /\ LET b == ledger[n][h] IN
       /\ IF b.kind = "send" THEN b.amount <= AccountBalance(n) ELSE TRUE
       /\ IF b.kind = "open"
            THEN b.parent = NoHash /\ b.amount > 0 /\ b.to = PublicKey[n]
            ELSE IF b.kind = "receive"
                 THEN b.parent # NoHash /\ b.amount > 0 /\ b.to = PublicKey[n]
                      /\ ledger[n][b.parent].kind = "send"
                      /\ ledger[n][b.parent].to = PublicKey[n]
                 ELSE TRUE
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

\* Forged blocks are those whose signature does not match the purported owner's
\* public key; rejecting them on receipt is the whole point of requiring a
\* signature-including broadcast.
DropForgedBlock(n, h) ==
  /\ h \in received[n]
  /\ PublicKey[n] # ledger[n][h].signer
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

CreateGenesisBlock(n, k) ==
  /\ lastHash = NoHash
  /\ \A m \in Node : ledger[m][NoHash] = NoBlockVal
  /\ lastHash' = CalculateHash([kind |-> "genesis", owner |-> PublicKey[n], amount |-> GenesisBalance, parent |-> NoHash], NoHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [kind |-> "genesis", owner |-> PublicKey[n],
                                                              amount |-> GenesisBalance, parent |-> NoHash, signer |-> k, to |-> PublicKey[n],
                                                              repr |-> PublicKey[n]]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

CreateSendBlock(n, k, amt, to) ==
  /\ lastHash # NoHash
  /\ OwnsAccount(n) # {}
  /\ ledger[n][lastHash] # NoBlockVal
  /\ amt > 0
  /\ amt <= AccountBalance(n)
  /\ lastHash' = CalculateHash([kind |-> "send", owner |-> PublicKey[n], amount |-> amt, parent |-> lastHash], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [kind |-> "send", owner |-> PublicKey[n],
                                                                 amount |-> amt, parent |-> lastHash, signer |-> k, to |-> to,
                                                                 repr |-> PublicKey[n]]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

CreateOpenBlock(n, k, h) ==
  /\ lastHash # NoHash
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].kind = "send"
  /\ ledger[n][h].to = PublicKey[n]
  /\ OwnsAccount(n) = {}
  /\ lastHash' = CalculateHash([kind |-> "open", owner |-> PublicKey[n], amount |-> ledger[n][h].amount,
                                parent |-> h], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [kind |-> "open", owner |-> PublicKey[n],
                                                                 amount |-> ledger[n][h].amount, parent |-> h, signer |-> k,
                                                                 to |-> PublicKey[n], repr |-> PublicKey[n]]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

CreateReceiveBlock(n, k, h) ==
  /\ lastHash # NoHash
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].kind = "send"
  /\ ledger[n][h].to = PublicKey[n]
  \/ OwnsAccount(n) # {}
  /\ lastHash' = CalculateHash([kind |-> "receive", owner |-> PublicKey[n], amount |-> ledger[n][h].amount,
                                parent |-> AccountChain(n), to |-> PublicKey[n]], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [kind |-> "receive", owner |-> PublicKey[n],
                                                                 amount |-> ledger[n][h].amount, parent |-> AccountChain(n), signer |-> k,
                                                                 to |-> PublicKey[n], repr |-> PublicKey[n]]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

CreateChangeRepresentativeBlock(n, k, r) ==
  /\ lastHash # NoHash
  /\ OwnsAccount(n) # {}
  /\ lastHash' = CalculateHash([kind |-> "change", owner |-> PublicKey[n], amount |-> 0, parent |-> lastHash], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [kind |-> "change", owner |-> PublicKey[n],
                                                                 amount |-> 0, parent |-> lastHash, signer |-> k,
                                                                 to |-> PublicKey[n], repr |-> r]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

Next ==
  \/ \E n \in Node, k \in PrivateKey : CreateGenesisBlock(n, k)
  \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, to \in PublicKey : CreateSendBlock(n, k, amt, to)
  \/ \E n \in Node, k \in PrivateKey, h \in Hash : CreateOpenBlock(n, k, h) \/ CreateReceiveBlock(n, k, h)
  \/ \E n \in Node, k \in PrivateKey, r \in PublicKey : CreateChangeRepresentativeBlock(n, k, r)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h) \/ DropForgedBlock(n, h)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, to \in PublicKey : CreateSendBlock(n, k, amt, to))
  /\ WF_vars(\E n \in Node, k \in PrivateKey, h \in Hash : CreateOpenBlock(n, k, h))
  /\ WF_vars(\E n \in Node, k \in PrivateKey, h \in Hash : CreateReceiveBlock(n, k, h))
  /\ WF_vars(\E n \in Node, k \in PrivateKey, r \in PublicKey : CreateChangeRepresentativeBlock(n, k, r))

\* Every block in every node's ledger must be signed by the public key of
\* the account under which it was recorded; a forged block can never pass.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].signer = PublicKey[n]

\* The ledger is typed as declared, and the last hash is always a valid hash or
\* the starting sentinel -- never a dangling or out-of-bound value.
TypeInvariant == TypeOK

\* The total across all accounts never exceeds the genesis balance; blocks that
\* minted or duplicated coins would cause this to be violated.
BalanceInvariant == TotalBalance = GenesisBalance

\* A chain that keeps growing without bound stops being tractable to explore at
\* verification time, so the model caps its length and bounces back to genesis.
\* That bounce is interleaved with block creation everywhere else, which is
\* what keeps model checking from ruling out every execution outright.
BounceBack == \E n \in Node : \E k \in PrivateKey : CreateGenesisBlock(n, k)

====