------------------------------ MODULE voldemort ------------------------------
(* /*Replicated storage protocol with clientside routing. *)
(* /*Debaditya Basak, 11 Nov 2016 *)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, ReadQ, WriteQ, FAILNUM
ASSUME N=5 /\ C=1 /\ STOP<10 /\ 1<=ReadQ /\ ReadQ<=3 
           /\ 1<=WriteQ /\ WriteQ<=3 /\ 0<=FAILNUM /\ FAILNUM<=2
Nodes == 1..N
Clients == N+1..N+C (* /*should give different ID space to Client *)

(*
--algorithm voldemort {
    variable FailNum = FAILNUM,
             state = "Reading",
             state1 = "InProcess",
             wQ = WriteQ,
             up = [n \in Nodes |-> TRUE], (* /*Initially all nodes are up *)
             db = [n \in Nodes |-> [ver |-> 0, val |-> 0]];
             (* /*All nodes have database, wherein [ver = 0, val = 0] stored for the item *)
             
    define {
    UpNodes == {i \in Nodes : up[i] = TRUE}
    ReturnReadQ == CHOOSE i \in SUBSET (UpNodes) : Cardinality(i) = ReadQ
    ReturnWriteQ == CHOOSE i \in SUBSET (UpNodes) : Cardinality(i) = WriteQ
    NodeR == CHOOSE i \in ReturnReadQ : \A j \in ReturnReadQ : db[i].ver >= db[j].ver
    NodeW(Q) == CHOOSE i \in Q : \A j \in Q : i <= j
    ClientNotWriting == state1 = "InProcess" /\ state = "Reading"
    ClientAtomicWriteDone == state="Writing" /\ state1="WriteEnd"
    }
    
    fair process (c \in Clients) 
    variable cntr = 0, hver = 0, Q = {};
    {
     CL: while (cntr <= STOP) {
          state := "Reading";
          state1 := "InProcess";
          cntr := cntr + 1;
          hver := db[NodeR].ver + 1;
          Q := ReturnWriteQ;          
          (* /*Nodes can fail or come back up between atomic states CL and CL1*)
          CL1: while (Q # {}) {
               state := "Writing";
               db[NodeW(Q)].ver := hver || db[NodeW(Q)].val := cntr;
               Q := Q \ {NodeW(Q)};
               if (Q = {}) {
                state1 := "WriteEnd";
                }
               }
         }
    }
    
    fair process (n \in Nodes)
    {
     NODE: while (TRUE /\ ClientNotWriting) { 
     (* /*To make Clients-process WRITE atomic *)
     (* /*Nodes state change only when ClientNotWriting is TRUE*)
           if (FailNum > 0 /\ up[self] = TRUE) { (* /*Storage node can fail *)
                up[self] := FALSE;
                FailNum := FailNum - 1;
                }
           else if (up[self] = FALSE) { (* /*Or recover *)
                up[self] := TRUE;
                FailNum := FailNum + 1;
                }
           }
    }
             
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES FailNum, state, state1, wQ, up, db, pc

(* define statement *)
UpNodes == {i \in Nodes : up[i] = TRUE}
ReturnReadQ == CHOOSE i \in SUBSET (UpNodes) : Cardinality(i) = ReadQ
ReturnWriteQ == CHOOSE i \in SUBSET (UpNodes) : Cardinality(i) = WriteQ
NodeR == CHOOSE i \in ReturnReadQ : \A j \in ReturnReadQ : db[i].ver >= db[j].ver
NodeW(Q) == CHOOSE i \in Q : \A j \in Q : i <= j
ClientNotWriting == state1 = "InProcess" /\ state = "Reading"
ClientAtomicWriteDone == state="Writing" /\ state1="WriteEnd"

VARIABLES cntr, hver, Q

vars == << FailNum, state, state1, wQ, up, db, pc, cntr, hver, Q >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ state = "Reading"
        /\ state1 = "InProcess"
        /\ wQ = WriteQ
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> [ver |-> 0, val |-> 0]]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> 0]
        /\ Q = [self \in Clients |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "CL"
                                        [] self \in Nodes -> "NODE"]

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self] <= STOP
                  THEN /\ state' = "Reading"
                       /\ state1' = "InProcess"
                       /\ cntr' = [cntr EXCEPT ![self] = cntr[self] + 1]
                       /\ hver' = [hver EXCEPT ![self] = db[NodeR].ver + 1]
                       /\ Q' = [Q EXCEPT ![self] = ReturnWriteQ]
                       /\ pc' = [pc EXCEPT ![self] = "CL1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << state, state1, cntr, hver, Q >>
            /\ UNCHANGED << FailNum, wQ, up, db >>

CL1(self) == /\ pc[self] = "CL1"
             /\ IF Q[self] # {}
                   THEN /\ state' = "Writing"
                        /\ db' = [db EXCEPT ![NodeW(Q[self])].ver = hver[self],
                                            ![NodeW(Q[self])].val = cntr[self]]
                        /\ Q' = [Q EXCEPT ![self] = Q[self] \ {NodeW(Q[self])}]
                        /\ IF Q'[self] = {}
                              THEN /\ state1' = "WriteEnd"
                              ELSE /\ TRUE
                                   /\ UNCHANGED state1
                        /\ pc' = [pc EXCEPT ![self] = "CL1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CL"]
                        /\ UNCHANGED << state, state1, db, Q >>
             /\ UNCHANGED << FailNum, wQ, up, cntr, hver >>

c(self) == CL(self) \/ CL1(self)

NODE(self) == /\ pc[self] = "NODE"
              /\ IF TRUE /\ ClientNotWriting
                    THEN /\ IF FailNum > 0 /\ up[self] = TRUE
                               THEN /\ up' = [up EXCEPT ![self] = FALSE]
                                    /\ FailNum' = FailNum - 1
                               ELSE /\ IF up[self] = FALSE
                                          THEN /\ up' = [up EXCEPT ![self] = TRUE]
                                               /\ FailNum' = FailNum + 1
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << FailNum, up >>
                         /\ pc' = [pc EXCEPT ![self] = "NODE"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << FailNum, up >>
              /\ UNCHANGED << state, state1, wQ, db, cntr, hver, Q >>

n(self) == NODE(self)

Next == (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
\* InvP is the Invariant function which checks db consistency after every atomic Client WRITE ends.
InvP == \A p \in Clients : (ClientAtomicWriteDone = TRUE => 
                                   (db[NodeR].ver = hver[p] /\ db[NodeR].val = cntr[p]))

=================================================================================
\* Observation: Model checking the system with FAILNUM = ReadQ and ReadQ = WriteQ
\*              causes it to violate the Invariant. This is evident, as, the size
\*              of WriteQ/ReadQ is then not enough to overcome the  node  failure
\*              count in case FAILNUM number of nodes fail. So say ReadQ/WriteQ=2
\*              and FAILNUM=2. In  this case the Client process  atomically Reads 
\*              the highest version from 2 ReadQ nodes, and fetches the WriteQ to 
\*              write the latest  entries into. But if  now the system decides to 
\*              fail  the two nodes  which were  selected as the WriteQ, the next 
\*              invocation of the Client process will write data to FAILED nodes. 
\*            - This is where the  Invariant will fail because it will try to get 
\*              the values  from a  ReadQ which  is not  consistent with nodes to 
\*              which the Client process is writing the latest updates to.
\*
\*            - The  Invariant  is  also  violated  if  ReadQ < = FAILNUM     and 
\*              WriteQ > FAILNUM. This is because even though WriteQ selects safe 
\*              number of  up-nodes  to  perform  the  writes,  the ReadQ is only 
\*              returning the  highest version from a  subset of nodes in WriteQ. 
\*              Thereby failing to return the true highest version that exists in 
\*              the up-nodes.
\*
\*            - So,  Invariant  will  only  be  satisfied  if FAILNUM < ReadQ and 
\*              FAILNUM< WriteQ. This is the pre-requisite that guarantees single
\*              -copy consistency in the system.
\*
\* teamMember:  Debaditya Basak, 50206177
