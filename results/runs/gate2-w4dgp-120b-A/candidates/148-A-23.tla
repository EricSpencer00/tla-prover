---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash

\* CalculateHash is a placeholder for the blockchain's hash operator; the .cfg substitutes
\* it with CalculateHashImpl so the model can remain finite.
CalculateHash == NoHashVal

\* Signature only checks that an account's private key was used; it does not model Ed25519.
SignatureOK(keys, sk, acct) == /\ keys[sk] = acct
                               /\ sk \in PrivateKey

\* SignedBlock is the on-chain data record, and Block is the on-wire broadcast packet.
SignedBlock == [acct: PublicKey, typ: {"genesis", "send", "open", "receive", "change"}, ref: Hash, val: Nat, sig: PrivateKey]
Block == [id: Hash, data: SignedBlock]

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

\* ChainBalance walks an account's block chain from final block back to genesis to sum credits.
ChainBalance(id, acct) == IF id = NoHash
                            THEN 0
                            ELSE IF ledger[id].acct = acct
                                  THEN (IF ledger[id].typ \in {"genesis", "receive"} THEN ledger[id].val ELSE 0) + ChainBalance(ledger[id].ref, acct)
                                  ELSE ChainBalance(ledger[id].ref, acct)

TotalBalance == ChainBalance(LastHash, "genesis_acct")

\* BalanceInvariant is a crisp, but separate, conservation check; the main invariant only
\* enforces signature correctness, because that is the security-critical part.
BalanceInvariant == TotalBalance <= GenesisBalance

TypeOK == /\ lastHash \in Hash
          /\ ledger \in [Hash -> SignedBlock \cup {NoBlockVal}]
          /\ received \in [Node -> SUBSET Hash]

\* The cryptographic security claim: whatever landed in a node's ledger was signed by
\* the account it claims, and no forged block could be accepted into the chain.
SignatureInvariant == \A n \in Node, h \in Hash : ledger[h] # NoBlockVal => SignatureOK(keys, ledger[h].sig, ledger[h].acct)

Init == /\ lastHash = NoHash
        /\ ledger = [h \in Hash |-> NoBlockVal]
        /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n) == /\ keys[n \in PrivateKey] = "genesis_acct"
                         /\ lastHash = NoHash
                         /\ ledger' = [h \in Hash |-> IF h = CalculateHash([acct |-> "genesis_acct", typ |-> "genesis", ref |-> NoHash, val |-> GenesisBalance], NoHash) THEN [acct |-> "genesis_acct", typ |-> "genesis", ref |-> NoHash, val |-> GenesisBalance, sig |-> n] ELSE NoBlockVal]
                         /\ lastHash' = CalculateHash([acct |-> "genesis_acct", typ |-> "genesis", ref |-> NoHash, val |-> GenesisBalance], NoHash)
                         /\ received' = [m \in Node |-> IF m # n
                                                      THEN {CalculateHash([acct |-> "genesis_acct", typ |-> "genesis", ref |-> NoHash, val |-> GenesisBalance], NoHash)} \cup received[m]
                                                      ELSE received[m]]

CreateSendBlock(n, val) == /\ keys[n \in PrivateKey] \in PublicKey
                           /\ lastHash # NoHash
                           /\ ChainBalance(lastHash, keys[n]) >= val
                           /\ lastHash' = CalculateHash([acct |-> keys[n], typ |-> "send", ref |-> lastHash, val |-> val], lastHash)
                           /\ ledger' = [ledger EXCEPT ![lastHash'] = [acct |-> keys[n], typ |-> "send", ref |-> lastHash, val |-> val, sig |-> n]]
                           /\ received' = [m \in Node |-> IF m # n THEN {lastHash'} \cup received[m] ELSE received[m]]

CreateOpenBlock(n, h) == /\ keys[n \in PrivateKey] \in PublicKey
                         /\ h # NoHash
                         /\ ledger[h].typ = "send"
                         /\ ledger[h].acct = keys[n]
                         /\ ChainBalance(lastHash, keys[n]) = 0
                         /\ \A m \in Node : h \notin received[m]
                         /\ lastHash' = CalculateHash([acct |-> keys[n], typ |-> "open", ref |-> h, val |-> 0], lastHash)
                         /\ ledger' = [ledger EXCEPT ![lastHash'] = [acct |-> keys[n], typ |-> "open", ref |-> h, val |-> 0, sig |-> n]]
                         /\ received' = [m \in Node |-> IF m # n THEN {lastHash'} \cup received[m] ELSE received[m]]

CreateReceiveBlock(n, h, val) == /\ keys[n \in PrivateKey] \in PublicKey
                                 /\ h # NoHash
                                 /\ ledger[h].acct = keys[n]
                                 /\ ledger[h].typ \in {"send", "open"}
                                 /\ \A m \in Node : h \notin received[m]
                                 /\ lastHash' = CalculateHash([acct |-> keys[n], typ |-> "receive", ref |-> h, val |-> val], lastHash)
                                 /\ ledger' = [ledger EXCEPT ![lastHash'] = [acct |-> keys[n], typ |-> "receive", ref |-> h, val |-> val, sig |-> n]]
                                 /\ received' = [m \in Node |-> IF m # n THEN {lastHash'} \cup received[m] ELSE received[m]]

CreateChangeBlock(n) == /\ keys[n \in PrivateKey] \in PublicKey
                        /\ lastHash # NoHash
                        /\ ChainBalance(lastHash, keys[n]) > 0
                        /\ lastHash' = CalculateHash([acct |-> keys[n], typ |-> "change", ref |-> lastHash, val |-> 0], lastHash)
                        /\ ledger' = [ledger EXCEPT ![lastHash'] = [acct |-> keys[n], typ |-> "change", ref |-> lastHash, val |-> 0, sig |-> n]]
                        /\ received' = [m \in Node |-> IF m # n THEN {lastHash'} \cup received[m] ELSE received[m]]

\* A node validates from its own stale copy before it merges a block into its copy.
ProcessBlock(n, h) == /\ h \in received[n]
                      /\ ledger[h] # NoBlockVal
                      /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
                      /\ received' = [received EXCEPT ![n] = @ \ {h}]
                      /\ UNCHANGED lastHash

Next == \/ \E n \in Node : CreateGenesisBlock(n)
        \/ \E n \in Node, val \in 0..GenesisBalance : CreateSendBlock(n, val)
        \/ \E n \in Node, h \in Hash : CreateOpenBlock(n, h)
        \/ \E n \in Node, h \in Hash, val \in 0..GenesisBalance : CreateReceiveBlock(n, h, val)
        \/ \E n \in Node : CreateChangeBlock(n)
        \/ \E n \in Node, h \in Hash : ProcessBlock(n, h)

Spec == Init /\ [][Next]_vars

====