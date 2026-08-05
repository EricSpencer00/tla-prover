---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Ed25519-style pubkey/privkey pair: PrivateKey derives its public key as PrivateKey.public.
\* Blake2b-style hash: CalculateHash maps block data and the previous hash to the next hash.
ASSUME CalculateHash \in [Hash -> (Hash \X PublicKey \X PUBLICATIONS) -> Hash]

PUBLICATIONS == {0, 1, 2}

VARIABLES lastHash, distributedLedger, received

vars == <<lastHash, distributedLedger, received>>

\* Block types on a Nano account chain: send, open, receive, and change-representative.
BlockType == {"send", "open", "receive", "change"}
Block == [type : BlockType, prev : Hash, source : PublicKey, amount : PUBLICATIONS, rep : PublicKey, sig : PublicKey]

Chain(n) == {b \in Block : b.source = n.publickey}
Blocks(n, h) == {b \in Chain(n) : b.prev = h}

\* Recursively walk an account chain backwards from a hash, summing all amounts it carries.
RECURSIVE SumBalance(_)
SumBalance(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN x.amount + SumBalance(S \ {x})
Balance(n) == SumBalance(Blocks(n, NoHash))

\* Genesis block always has a sender and receiver of the same key.
GenesisSender(n) == n.privatekey.publickey
GenesisRecipient(n) == n.privatekey.publickey

TypeOK ==
  /\ lastHash \in Hash
  /\ distributedLedger \in [Hash -> [Node -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ distributedLedger = [h \in Hash |-> [n \in Node |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesis(n) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash(NoHashVal, GenesisSender(n), [type |-> "open", prev |-> NoHash, source |-> GenesisSender(n), amount |-> GenesisBalance, rep |-> GenesisRecipient(n), sig |-> GenesisSender(n)])
  /\ distributedLedger' = [h \in Hash |-> [m \in Node |-> IF h = lastHash' THEN [type |-> "open", prev |-> NoHash, source |-> GenesisSender(n), amount |-> GenesisBalance, rep |-> GenesisRecipient(n), sig |-> GenesisSender(n)] ELSE NoBlockVal] ]
  /\ UNCHANGED received

CreateSend(n) ==
  /\ lastHash # NoHashVal
  /\ Balance(n.privatekey.publickey) >= 1
  /\ lastHash' = CalculateHash(lastHash, n.privatekey.publickey, [type |-> "send", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 1, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey])
  /\ distributedLedger' = [distributedLedger EXCEPT ![lastHash'] = [m \in Node |-> [type |-> "send", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 1, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED <<>>

CreateOpen(n) ==
  /\ \E h \in Hash : distributedLedger[h][n] # NoBlockVal /\ distributedLedger[h][n].type = "send" /\ distributedLedger[h][n].source # n.privatekey.publickey /\ ~ \E g \in Hash : distributedLedger[g][n] # NoBlockVal /\ distributedLedger[g][n].type = "open"
  /\ lastHash' = CalculateHash(lastHash, n.privatekey.publickey, [type |-> "open", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 1, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey])
  /\ distributedLedger' = [distributedLedger EXCEPT ![lastHash'] = [m \in Node |-> [type |-> "open", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 1, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED <<>>

CreateReceive(n) ==
  /\ \E h \in Hash : distributedLedger[h][n] # NoBlockVal /\ distributedLedger[h][n].type = "send" /\ ~ \E g \in Hash : distributedLedger[g][n] # NoBlockVal /\ distributedLedger[g][n].type = "receive" /\ Balance(n.privatekey.publickey) >= 1
  /\ lastHash' = CalculateHash(lastHash, n.privatekey.publickey, [type |-> "receive", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 1, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey])
  /\ distributedLedger' = [distributedLedger EXCEPT ![lastHash'] = [m \in Node |-> [type |-> "receive", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 1, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED <<>>

CreateChange(n) ==
  /\ lastHash' = CalculateHash(lastHash, n.privatekey.publickey, [type |-> "change", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 0, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey])
  /\ distributedLedger' = [distributedLedger EXCEPT ![lastHash'] = [m \in Node |-> [type |-> "change", prev |-> lastHash, source |-> n.privatekey.publickey, amount |-> 0, rep |-> n.privatekey.publickey, sig |-> n.privatekey.publickey]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED <<>>

\* Validation checks: cryptographic signature, block existence, and block-type-specific rules.
Validate(n, h) ==
  /\ h \in received[n]
  /\ distributedLedger[h][n].sig = distributedLedger[h][n].source
  /\ distributedLedger[h][n].prev = NoHash \/ distributedLedger[distributedLedger[h][n].prev][n] # NoBlockVal
  /\ (distributedLedger[h][n].type = "send" => Balance(n.privatekey.publickey) >= 1)
  /\ (distributedLedger[h][n].type = "receive" => ~ \E g \in Hash : distributedLedger[g][n] # NoBlockVal /\ distributedLedger[g][n].type = "receive")
  /\ distributedLedger' = [distributedLedger EXCEPT ![h] = [m \in Node |-> [type |-> distributedLedger[h][n].type, prev |-> distributedLedger[h][n].prev, source |-> distributedLedger[h][n].source, amount |-> distributedLedger[h][n].amount, rep |-> distributedLedger[h][n].rep, sig |-> distributedLedger[h][n].sig]]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesis(n) \/ CreateSend(n) \/ CreateOpen(n) \/ CreateReceive(n) \/ CreateChange(n)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* Every block committed to any local ledger copy has a valid signature matching its account's public key.
SafetyInvariant == \A h \in Hash : \A n \in Node : distributedLedger[h][n] # NoBlockVal => distributedLedger[h][n].sig = distributedLedger[h][n].source

====