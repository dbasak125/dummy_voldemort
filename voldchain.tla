------------------------------ MODULE voldchain ------------------------------
(* /*Replicated storage protocol with chain replication. *)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, FAILNUM
ASSUME N - FAILNUM >= 1 /\ STOP < 5 /\ 0 <= FAILNUM /\ FAILNUM <= 2
Nodes == 1..N
Clients == N+1..N+C (* /*should give different ID space to Client *)
Procs == 1..N + C
Configurator == N + C + 1 (* /*Configurator is unfallable *)

(*
--algorithm voldchain {
    variable FailNum = FAILNUM,
             msg = [j \in Procs |-> <<"X",-1,-1,"X",-1>>], (* /*default message *)
             up = [n \in Nodes |-> TRUE],
             db = [n \in Nodes |-> [ver |-> -1, val |-> -1, cli |-> -1]],
             (* /*db is single record only *)
             chain = <<1>>,
             (* /*chain is a sequence initially empty *)
             status = "Writing";
             
    define {
    UpNodes == {n \in Nodes : up[n] = TRUE}
    InChain(s) == \E i \in 1..Len(chain) : chain[i] = s
    ChainNodes == {chain[j] : j \in 1..Len(chain)}
    FreeUpNode == IF (UpNodes \ ChainNodes) # {} THEN 
                  CHOOSE i \in (UpNodes \ ChainNodes) : i > 0 
                  ELSE 0
    GetIndex(s) == CHOOSE i \in 1..Len(chain) : chain[i] = s
    (* /*Assume InChain(s), returns index of s in chain *)
    GetNext(s) == chain[GetIndex(s)+1]
    (* /*Assume InChain(s), returns successor of s in chain *)
    IsUp(s) == up[s] = TRUE
    }
    
    fair process (c \in Clients) (* /*Client process *)
    variable ctr = -1, hver = -1;
    {
     C0: await (Len(chain) > 0); 
     CL: while (ctr <= STOP) { 
         status := "Reading";
         CLR: hver := db[chain[Len(chain)]].ver + 1;
              ctr := ctr + 1;
         CLW: while (msg[self][1] # "ACK" \/ 
                     msg[self][2] # hver \/ 
                     msg[self][3] # ctr \/ 
                     msg[self][4] # "UPDATE") {
                       msg[chain[1]] := <<"SYN",hver,ctr,"UPDATE",self>>;                         
                     };
              status := "Writing";
              msg[self] := <<"X",-1,-1,"X",-1>>;
         };
    }
    
    fair process (n \in Nodes) (* /*Storage node *)
    {
     ND: while (TRUE) { 
         either 
         NM: { if (msg[self][1] = "SYN" /\ Len(chain) > 0) { 
               (* /*react to message *)
                 if (self = chain[Len(chain)] /\ msg[self][4] = "QUERY") {
                   msg[msg[self][5]] := <<"ACK",db[self].ver,db[self].val,"QUERY",self>> ||
                   msg[self] := <<"X",-1,-1,"X",-1>>;
                 }
                 else if (self = chain[Len(chain)] /\ msg[self][4] = "UPDATE") {
                   db[self].ver := msg[self][2] || db[self].val := msg[self][3];
                   msg[msg[self][5]] := <<"ACK",db[self].ver,db[self].val,"UPDATE",self>> ||
                   msg[self] := <<"X",-1,-1,"X",-1>>;
                 }
                 else if (self # chain[Len(chain)] /\ 
                          msg[self][4] = "UPDATE" /\ InChain(self) = TRUE) {
                   db[self].ver := msg[self][2] || db[self].val := msg[self][3];
                   msg[GetNext(self)] := 
                   <<"SYN",msg[self][2],msg[self][3],"UPDATE",msg[self][5]>> ||
                   msg[self] := <<"X",-1,-1,"X",-1>>;
                 }
               }
         } or
         NDF: {
                if (FailNum > 0 /\ up[self] = TRUE) { (* /*Storage node can fail *)
                  up[self] := FALSE;
                  FailNum := FailNum - 1; }
                else if (up[self] = FALSE) { (* /*Or recover *)
                  up[self] := TRUE;
                  msg[self] := <<"X",-1,-1,"X",-1>>; 
                  FailNum := FailNum + 1; }
           }
     };
    }
    
    fair process (p = Configurator) (* /*Maintain the chain *)
    variables un = 0;
    {
     P: while(TRUE) {
        if (Len(chain) = 0) {
          chain := Append(chain,FreeUpNode); }
        else if (Len(chain) < 3 /\ FreeUpNode > 0) {
          un := FreeUpNode;
          db[un].ver := db[chain[Len(chain)]].ver 
          || db[un].val := db[chain[Len(chain)]].val 
          || db[un].cli := db[chain[Len(chain)]].cli;
          chain := Append(SelectSeq(chain,IsUp),FreeUpNode); }        
        else if (Len(chain) > 0) {
          chain := SelectSeq(chain,IsUp); }
     };
    }
             
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES FailNum, msg, up, db, chain, status, pc

(* define statement *)
UpNodes == {n \in Nodes : up[n] = TRUE}
InChain(s) == \E i \in 1..Len(chain) : chain[i] = s
ChainNodes == {chain[j] : j \in 1..Len(chain)}
FreeUpNode == IF (UpNodes \ ChainNodes) # {} THEN
              CHOOSE i \in (UpNodes \ ChainNodes) : i > 0
              ELSE 0
GetIndex(s) == CHOOSE i \in 1..Len(chain) : chain[i] = s

GetNext(s) == chain[GetIndex(s)+1]

IsUp(s) == up[s] = TRUE

VARIABLES ctr, hver, un

vars == << FailNum, msg, up, db, chain, status, pc, ctr, hver, un >>

ProcSet == (Clients) \cup (Nodes) \cup {Configurator}

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ msg = [j \in Procs |-> <<"X",-1,-1,"X",-1>>]
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> [ver |-> -1, val |-> -1, cli |-> -1]]
        /\ chain = <<1>>
        /\ status = "Writing"
        (* Process c *)
        /\ ctr = [self \in Clients |-> -1]
        /\ hver = [self \in Clients |-> -1]
        (* Process p *)
        /\ un = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "C0"
                                        [] self \in Nodes -> "ND"
                                        [] self = Configurator -> "P"]

C0(self) == /\ pc[self] = "C0"
            /\ (Len(chain) > 0)
            /\ pc' = [pc EXCEPT ![self] = "CL"]
            /\ UNCHANGED << FailNum, msg, up, db, chain, status, ctr, hver, un >>

CL(self) == /\ pc[self] = "CL"
            /\ IF ctr[self] <= STOP
                  THEN /\ status' = "Reading"
                       /\ pc' = [pc EXCEPT ![self] = "CLR"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED status
            /\ UNCHANGED << FailNum, msg, up, db, chain, ctr, hver, un >>

CLR(self) == /\ pc[self] = "CLR"
             /\ hver' = [hver EXCEPT ![self] = db[chain[Len(chain)]].ver + 1]
             /\ ctr' = [ctr EXCEPT ![self] = ctr[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "CLW"]
             /\ UNCHANGED << FailNum, msg, up, db, chain, status, un >>

CLW(self) == /\ pc[self] = "CLW"
             /\ IF msg[self][1] # "ACK" \/
                   msg[self][2] # hver[self] \/
                   msg[self][3] # ctr[self] \/
                   msg[self][4] # "UPDATE"
                   THEN /\ msg' = [msg EXCEPT ![chain[1]] = <<"SYN",hver[self],ctr[self],"UPDATE",self>>]
                        /\ pc' = [pc EXCEPT ![self] = "CLW"]
                        /\ UNCHANGED status
                   ELSE /\ status' = "Writing"
                        /\ msg' = [msg EXCEPT ![self] = <<"X",-1,-1,"X",-1>>]
                        /\ pc' = [pc EXCEPT ![self] = "CL"]
             /\ UNCHANGED << FailNum, up, db, chain, ctr, hver, un >>

c(self) == C0(self) \/ CL(self) \/ CLR(self) \/ CLW(self)

ND(self) == /\ pc[self] = "ND"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "NM"]
               \/ /\ pc' = [pc EXCEPT ![self] = "NDF"]
            /\ UNCHANGED << FailNum, msg, up, db, chain, status, ctr, hver, un >>

NM(self) == /\ pc[self] = "NM"
            /\ IF msg[self][1] = "SYN" /\ Len(chain) > 0
                  THEN /\ IF self = chain[Len(chain)] /\ msg[self][4] = "QUERY"
                             THEN /\ msg' = [msg EXCEPT ![msg[self][5]] = <<"ACK",db[self].ver,db[self].val,"QUERY",self>>,
                                                        ![self] = <<"X",-1,-1,"X",-1>>]
                                  /\ db' = db
                             ELSE /\ IF self = chain[Len(chain)] /\ msg[self][4] = "UPDATE"
                                        THEN /\ db' = [db EXCEPT ![self].ver = msg[self][2],
                                                                 ![self].val = msg[self][3]]
                                             /\ msg' = [msg EXCEPT ![msg[self][5]] = <<"ACK",db'[self].ver,db'[self].val,"UPDATE",self>>,
                                                                   ![self] = <<"X",-1,-1,"X",-1>>]
                                        ELSE /\ IF self # chain[Len(chain)] /\
                                                   msg[self][4] = "UPDATE" /\ InChain(self) = TRUE
                                                   THEN /\ db' = [db EXCEPT ![self].ver = msg[self][2],
                                                                            ![self].val = msg[self][3]]
                                                        /\ msg' = [msg EXCEPT ![GetNext(self)] = <<"SYN",msg[self][2],msg[self][3],"UPDATE",msg[self][5]>>,
                                                                              ![self] = <<"X",-1,-1,"X",-1>>]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << msg, 
                                                                        db >>
                  ELSE /\ TRUE
                       /\ UNCHANGED << msg, db >>
            /\ pc' = [pc EXCEPT ![self] = "ND"]
            /\ UNCHANGED << FailNum, up, chain, status, ctr, hver, un >>

NDF(self) == /\ pc[self] = "NDF"
             /\ IF FailNum > 0 /\ up[self] = TRUE
                   THEN /\ up' = [up EXCEPT ![self] = FALSE]
                        /\ FailNum' = FailNum - 1
                        /\ msg' = msg
                   ELSE /\ IF up[self] = FALSE
                              THEN /\ up' = [up EXCEPT ![self] = TRUE]
                                   /\ msg' = [msg EXCEPT ![self] = <<"X",-1,-1,"X",-1>>]
                                   /\ FailNum' = FailNum + 1
                              ELSE /\ TRUE
                                   /\ UNCHANGED << FailNum, msg, up >>
             /\ pc' = [pc EXCEPT ![self] = "ND"]
             /\ UNCHANGED << db, chain, status, ctr, hver, un >>

n(self) == ND(self) \/ NM(self) \/ NDF(self)

P == /\ pc[Configurator] = "P"
     /\ IF Len(chain) = 0
           THEN /\ chain' = Append(chain,FreeUpNode)
                /\ UNCHANGED << db, un >>
           ELSE /\ IF Len(chain) < 3 /\ FreeUpNode > 0
                      THEN /\ un' = FreeUpNode
                           /\ db' = [db EXCEPT ![un'].ver = db[chain[Len(chain)]].ver,
                                               ![un'].val = db[chain[Len(chain)]].val,
                                               ![un'].cli = db[chain[Len(chain)]].cli]
                           /\ chain' = Append(SelectSeq(chain,IsUp),FreeUpNode)
                      ELSE /\ IF Len(chain) > 0
                                 THEN /\ chain' = SelectSeq(chain,IsUp)
                                 ELSE /\ TRUE
                                      /\ chain' = chain
                           /\ UNCHANGED << db, un >>
     /\ pc' = [pc EXCEPT ![Configurator] = "P"]
     /\ UNCHANGED << FailNum, msg, up, status, ctr, hver >>

p == P

Next == p
           \/ (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))
        /\ WF_vars(p)

\* END TRANSLATION
Invariant_1 == \A cl \in Clients : (status = "Writing" => 
            (hver[cl] = db[chain[Len(chain)]].ver /\ ctr[cl] = db[chain[Len(chain)]].val))
Invariant_2 == \A nl \in 1..Len(chain)-1 : ((Len(chain) > 1) => (db[chain[nl]].ver >= db[chain[nl+1]].ver))
Invariant_3 == \A cl \in Clients : (status = "Writing" => (\E jk \in Nodes : db[jk].ver = -1))
=============================================================================
(*  Observations:
    This project is server side routing, which acted as a black box to client-
    systems. This is different to Project 1 where global variables were used to do 
    client side routing. Also there were no configurator in Project1 as all the 
    responsibilities for data management was being done by the client. In this case
    (theoretically), a dedicated PAXOS based configurator is deployed to maintain 
    the state of replicated chain. However in this project, configurator is not 
    directly accessed by nodes, which posed its own challenges to define what constitutes
    an active tail or head node. We here, always consider current chain config while 
    identifying head or tail. 
1.  As clients were not supposed to communicate with configurator for this 
    project, deciding active head and tail was a big challange.
2.  The assumption that atleast one node will be up all the time was a huge 
    help in calculation of head and tail.
3.  We faced problems while initializing the system and came to conclusion 
    that system should always intialize with n nodes such that n+1>FAILNUM (At least
    one node should be up for system to sustain consistent behavior).
4.  Initializing with 1 or two nodes in this case was voilating consistency 
    as both nodes can go down (because fo FAILNUM) and entire service will go 
    down and system will loose data.
5.  In case of 2 clients problem arises when say client_1 read ver 3 and could 
    not proceed to write. Meanwhile client_2 kept on reading and writing till 
    it finish up writing lets say 5. And if now client_1 writes its data that will 
    violate consistency for client_2.
6.  Again after lot of test we found a case when configurator process is not
    getting picked; meanwhile a node went down and after a write cycle it comes 
    back on (This causes the tail to fail and come back up with its db reset to default - 
    while the configurator did not remove/re-configure nodes as of yet).
    Because of this one of the invariant_1 is failing but we feel that this 
    the limitation of this system design in the requirements. 
7.  A better design would be nodes communicating with configurator to get details 
    about successors and copying etc.
8.  Voldchain is more fail safe(fault tolerant) when compared with project 1, as it 
    can still serve with single up node.
9.  In Voldchain, tailnode is analogus to readQ (in project 1) and headnode is 
    analogus to the writeQ. Server side routing is hence more fault tolerant with 
    even lesser number of nodes required for maintaining single copy consistency.
10. In Project1 failnum must be less than the size of readQ, but voldchain can 
    work with 1 upnode as discussed above.
11. Also 2 clients scenario will fail invariant_1 as db of node can be consistant with
    only one client at a time and not with all of them.
*)
\* teamMember_1:  Debaditya Basak, 50206177
\* teamMember_2:  Divyank Sharma, 50207091
