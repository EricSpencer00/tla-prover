---- MODULE 25_client_server_db_ae ----
\* benchmark: pyv-client-server-db-ae

EXTENDS TLC, FiniteSetTheorems, TLAPS

CONSTANT Node
CONSTANT Request
CONSTANT Response
CONSTANT DbRequestId

VARIABLE match

VARIABLE request_sent
VARIABLE response_sent
VARIABLE response_received

VARIABLE db_request_sent
VARIABLE db_response_sent

VARIABLE t

vars == <<match,request_sent,response_sent,response_received,db_request_sent,db_response_sent,t>>

NoneWithId(i) == \A n \in Node : <<i,n>> \notin t
ResponseMatched(n,p) == \E r \in Request : (<<n,r>> \in request_sent) /\ <<r,p>> \in match


NewRequest(n, r) ==
    /\ request_sent' = request_sent \cup {<<n,r>>}
    /\ UNCHANGED <<match,response_sent,response_received,db_request_sent,db_response_sent,t>>

ServerProcessRequest(n,r,i) ==
    /\ <<n,r>> \in request_sent
    /\ NoneWithId(i)
    /\ t' = t \cup {<<i,n>>}
    /\ db_request_sent' = db_request_sent \cup {<<i,r>>}
    /\ UNCHANGED <<match,request_sent,response_sent,response_received,db_response_sent>>

DbProcessRequest(i,r,p) ==
    /\ <<i,r>> \in db_request_sent
    /\ <<r,p>> \in match
    /\ db_response_sent' = db_response_sent \cup {<<i,p>>}
    /\ UNCHANGED <<match,request_sent,response_sent,response_received,db_request_sent,t>>

ServerProcessDbResponse(n,i,p) ==
    /\ <<i,p>> \in db_response_sent
    /\ <<i,n>> \in t
    /\ response_sent' = response_sent \cup {<<n,p>>}
    /\ UNCHANGED <<match,request_sent,response_received,db_request_sent,db_response_sent,t>>

ReceiveResponse(n,p) == 
    /\ <<n,p>> \in response_sent
    /\ response_received' = response_received \cup {<<n,p>>}
    /\ UNCHANGED <<match,request_sent,response_sent,db_request_sent,db_response_sent,t>>

Next ==
    \/ \E n \in Node, r \in Request : NewRequest(n,r)
    \/ \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
    \/ \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
    \/ \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
    \/ \E n \in Node, p \in Response : ReceiveResponse(n,p)

Init == 
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent = {}
    /\ response_sent = {}
    /\ response_received = {}
    /\ db_request_sent = {}
    /\ db_response_sent = {}
    /\ t = {}

TypeOK ==
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent \in SUBSET (Node \X Request)
    /\ response_sent \in SUBSET (Node \X Response)
    /\ response_received \in SUBSET (Node \X Response)
    /\ db_request_sent \in SUBSET (DbRequestId \X Request)
    /\ db_response_sent \in SUBSET (DbRequestId \X Response)
    /\ t \in SUBSET (DbRequestId \X Node)

\* TypeOKRandom ==
\*     /\ match \in RandomSubset(20, SUBSET (Request \X Response))
\*     /\ request_sent \in RandomSubset(10, SUBSET (Node \X Request))
\*     /\ response_sent \in RandomSubset(10, SUBSET (Node \X Response))
\*     /\ response_received \in RandomSubset(10, SUBSET (Node \X Response))
\*     /\ db_request_sent \in RandomSubset(10, SUBSET (DbRequestId \X Request))
\*     /\ db_response_sent \in RandomSetOfSubsets(10, 4, (DbRequestId \X Response))
\*     /\ t \in RandomSetOfSubsets(10, 5, (DbRequestId \X Node))

Safety == \A n \in Node, p \in Response : (<<n,p>> \in response_received) => ResponseMatched(n,p)

Symmetry == Permutations(Node) \cup Permutations(Request) \cup Permutations(Response) \cup Permutations(DbRequestId)

NextUnchanged == UNCHANGED vars

Test == response_received = {}

\* Inductive strengthening conjuncts
Inv273_1_0_def == \A VARI \in Node : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARI,VARP>> \in response_sent))
Inv209_1_1_def == \A VARJ \in Node : \A VARP \in Response : (<<VARJ,VARP>> \in response_sent) \/ (~(<<VARJ,VARP>> \in response_received))
Inv3082_2_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARJ \in Node : (VARI=VARJ /\ match = match) \/ (~(<<VARID,VARI>> \in t)) \/ (~(<<VARID,VARJ>> \in t))
Inv380_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : ~(<<VARID,VARP>> \in db_response_sent) \/ (~(NoneWithId(VARID)))
Inv388_1_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : ~(<<VARID,VARR>> \in db_request_sent) \/ (~(NoneWithId(VARID)))
Inv2868_2_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARID,VARI>> \in t) \/ (~(<<VARID,VARP>> \in db_response_sent)))
Inv873_2_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : (<<VARI,VARR>> \in request_sent) \/ (~(<<VARID,VARI>> \in t)) \/ (~(<<VARID,VARR>> \in db_request_sent))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv273_1_0_def
  /\ Inv209_1_1_def
  /\ Inv3082_2_2_def
  /\ Inv380_1_0_def
  /\ Inv388_1_1_def
  /\ Inv2868_2_2_def
  /\ Inv873_2_3_def

ASSUME Fin == IsFiniteSet(Node) /\ IsFiniteSet(Request) /\ IsFiniteSet(Response) /\ IsFiniteSet(DbRequestId)
ASSUME Nonempty == Request # {} /\ Response # {} /\ Node # {} /\ DbRequestId # {}


THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY DEF vars, NoneWithId, ResponseMatched, NewRequest, ServerProcessRequest, DbProcessRequest, ServerProcessDbResponse, ReceiveResponse, Next, Init, TypeOK, Safety, Symmetry, NextUnchanged, Test, Inv273_1_0_def, Inv209_1_1_def, Inv3082_2_2_def, Inv380_1_0_def, Inv388_1_1_def, Inv2868_2_2_def, Inv873_2_3_def, IndAuto
====