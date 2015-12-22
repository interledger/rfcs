------------------------------- MODULE Atomic -------------------------------
(***************************************************************************)
(* Formal Specification in TLA^+ of the                                    *)
(* Interledger Protocol Atomic (ILP/A)                                     *)
(*                                                                         *)
(*`.                                                                       *)
(* Modeled after the excellent Raft specification by Diego Ongaro.         *)
(*   Available at https://github.com/ongardie/raft.tla                     *)
(*                                                                         *)
(*   Copyright 2014 Diego Ongaro.                                          *)
(*   This work is licensed under the Creative Commons Attribution-4.0      *)
(*   International License https://creativecommons.org/licenses/by/4.0/  .'*)
(***************************************************************************)

EXTENDS Naturals, Sequences, Bags, TLC

\* The set of ledger IDs
CONSTANTS Ledger

\* The set of participant IDs
CONSTANTS Participant

\* The notary
CONSTANTS Notary

\* Sender states
CONSTANTS S_Ready, S_Waiting, S_Done

\* Notary states
CONSTANTS N_Waiting, N_Committed, N_Aborted

\* Notary decisions
CONSTANTS D_Execute, D_Abort

\* Ledger states
CONSTANTS L_Proposed, L_Prepared, L_Executed, L_Aborted

\* Message types
CONSTANTS M_PrepareRequest, M_ExecuteRequest, M_AbortRequest,
          M_PrepareNotify, M_ExecuteNotify, M_AbortNotify,
          M_SubmitReceiptRequest

\* Receipt signature
CONSTANTS R_ReceiptSignature

----
\* Global variables

\* A bag of records representing requests and responses sent from one process
\* to another
VARIABLE messages

----
\* Sender variables

\* State of the sender (S_Ready, S_Waiting, S_Done)
VARIABLE senderState

\* All sender variables
senderVars == <<senderState>>
----
\* The following variables are all per ledger (functions with domain Ledger)

\* The ledger state (L_Proposed, L_Prepared, L_Executed or L_Aborted)
VARIABLE ledgerState

\* All ledger variables
ledgerVars == <<ledgerState>>
----
\* Notary variables

\* State of the notary (N_Waiting, N_Committed, N_Aborted)
VARIABLE notaryState

\* All notary variables
notaryVars == <<notaryState>>
----

\* All variables; used for stuttering (asserting state hasn't changed)
vars == <<messages, senderVars, ledgerVars, notaryVars>>

----
\* Helpers

\* Add a set of new messages in transit
Broadcast(m) == messages' = messages (+) SetToBag(m)

\* Add a message to the bag of messages
Send(m) == Broadcast({m})

\* Remove a message from the bag of messages. Used when a process is done
\* processing a message.
Discard(m) == messages' = messages (-) SetToBag({m})

\* Respond to a message by sending multiple messages
ReplyBroadcast(responses, request) ==
    messages' = messages (-) SetToBag({request}) (+) SetToBag(responses)

\* Combination of Send and Discard
Reply(response, request) ==
    ReplyBroadcast({response}, request)


\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Is a final ledger state
IsFinalLedgerState(i) == i \in {L_Executed, L_Aborted}

\* Sender
Sender == Min(Participant)

\* Recipient
Recipient == Max(Participant)

\* Set of connectors
Connector == Participant \ {Sender, Recipient}

----
\* Define type specification for all variables

TypeOK == /\ IsABag(messages)
          /\ senderState \in {S_Ready, S_Waiting, S_Done}
          /\ ledgerState \in [Ledger -> {L_Proposed, L_Prepared, L_Executed, L_Aborted}]

Consistency ==
    \A l1, l2 \in Ledger : \lnot /\ ledgerState[l1] = L_Aborted
                                 /\ ledgerState[l2] = L_Executed

Inv == /\ TypeOK
       /\ Consistency

----
\* Define initial values for all variables

InitSenderVars == /\ senderState = S_Ready

InitLedgerVars == /\ ledgerState = [i \in Ledger |-> L_Proposed]

InitNotaryVars == /\ notaryState = N_Waiting

Init == /\ messages = EmptyBag
        /\ InitSenderVars
        /\ InitLedgerVars
        /\ InitNotaryVars

----
\* Define state transitions

\* Participant i starts off the chain
Start(i) ==
    /\ senderState = S_Ready
    /\ senderState' = S_Waiting
    /\ Send([mtype   |-> M_PrepareRequest,
             msource |-> i,
             mdest   |-> i+1])
    /\ UNCHANGED <<ledgerVars, notaryVars>>

\* Notary times out
NotaryTimeout ==
    /\ notaryState = N_Waiting
    /\ notaryState' = N_Aborted
    /\ Broadcast(
            {[mtype    |-> M_AbortRequest,
              msource  |-> Notary,
              mdest    |-> k,
              msig     |-> D_Abort] : k \in Ledger})
    /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger spontaneously aborts
LedgerAbort(l) ==
    /\ ledgerState[l] = L_Proposed
    /\ ledgerState' = [ledgerState EXCEPT ![l] = L_Aborted]
    /\ Send([mtype   |-> M_AbortNotify,
             msource |-> l,
             mdest   |-> l-1])
    /\ UNCHANGED <<senderVars, notaryVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Ledger i receives a Prepare request from process j
LedgerHandlePrepareRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Proposed
                 /\ j = i - 1
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Prepared]
          /\ Reply([mtype   |-> M_PrepareNotify,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars, notaryVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger i receives an Execute request from process j
LedgerHandleExecuteRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Prepared
                 /\ m.msig = D_Execute
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Executed]
          /\ Reply([mtype   |-> M_ExecuteNotify,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<senderVars, notaryVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger i receives an Abort request from process j
LedgerHandleAbortRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] \in { L_Proposed, L_Prepared }
                 /\ m.msig = D_Abort
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Aborted]
          /\ Reply([mtype   |-> M_AbortNotify,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<senderVars, notaryVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger i receives a message
LedgerReceive(i, j, m) ==
    \/ /\ m.mtype = M_PrepareRequest
       /\ LedgerHandlePrepareRequest(i, j, m)
    \/ /\ m.mtype = M_ExecuteRequest
       /\ LedgerHandleExecuteRequest(i, j, m)
    \/ /\ m.mtype = M_AbortRequest
       /\ LedgerHandleAbortRequest(i, j, m)

\* Ledger j notifies sender that the transfer is executed
SenderHandleExecuteNotify(i, j, m) ==
    \/ /\ senderState = S_Waiting
       /\ senderState' = S_Done
       /\ Discard(m)
       /\ UNCHANGED <<ledgerVars, notaryVars>>
    \/ /\ senderState # S_Waiting
       /\ Discard(m)
       /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger j notifies sender that the transfer is aborted
SenderHandleAbortNotify(i, j, m) ==
    LET isSenderWaiting == senderState \in { S_Waiting, S_Ready }
    IN \/ /\ isSenderWaiting
          /\ senderState' = S_Done
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars, notaryVars>>
       \/ /\ \lnot isSenderWaiting
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Sender receives a message
SenderReceive(i, j, m) ==
    \/ /\ m.mtype = M_ExecuteNotify
       /\ SenderHandleExecuteNotify(i, j, m)
    \/ /\ m.mtype = M_AbortNotify
       /\ SenderHandleAbortNotify(i, j, m)

\* Ledger j notifies recipient that the transfer is prepared
RecipientHandlePrepareNotify(i, j, m) ==
    /\ Reply([mtype    |-> M_SubmitReceiptRequest,
              msource  |-> i,
              mdest    |-> Notary,
              mreceipt |-> R_ReceiptSignature], m)
    /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Recipient receives a message
RecipientReceive(i, j, m) ==
    /\ m.mtype = M_PrepareNotify
    /\ RecipientHandlePrepareNotify(i, j, m)

\* Ledger j notifies connector i that the transfer is prepared
ConnectorHandlePrepareNotify(i, j, m) ==
    /\ Reply([mtype   |-> M_PrepareRequest,
              msource |-> i,
              mdest   |-> i+1], m)
    /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger j notifies connector i that the transfer is executed
ConnectorHandleExecuteNotify(i, j, m) ==
    /\ Discard(m)
    /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger j notifies connector i that the transfer is aborted
ConnectorHandleAbortNotify(i, j, m) ==
    /\ Discard(m)
    /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Connector receives a message
ConnectorReceive(i, j, m) ==
    \/ /\ m.mtype = M_PrepareNotify
       /\ ConnectorHandlePrepareNotify(i, j, m)
    \/ /\ m.mtype = M_ExecuteNotify
       /\ ConnectorHandleExecuteNotify(i, j, m)
    \/ /\ m.mtype = M_AbortNotify
       /\ ConnectorHandleAbortNotify(i, j, m)

\* Notary receives a signed receipt
NotaryHandleSubmitReceiptRequest(i, j, m) ==
    \/ /\ m.mreceipt = R_ReceiptSignature
       /\ notaryState = N_Waiting
       /\ notaryState' = N_Committed
       /\ ReplyBroadcast(
            {[mtype    |-> M_ExecuteRequest,
              msource  |-> i,
              mdest    |-> k,
              msig     |-> D_Execute] : k \in Ledger}, m)
       /\ UNCHANGED <<senderVars, ledgerVars>>
    \/ /\ notaryState # N_Waiting
       /\ Discard(m)
       /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Notary receives a message
NotaryReceive(i, j, m) ==
    /\ m.mtype = M_SubmitReceiptRequest
    /\ NotaryHandleSubmitReceiptRequest(i, j, m)

\* Receive a message
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ /\ i \in Ledger
          /\ LedgerReceive(i, j, m)
       \/ /\ i = Sender
          /\ SenderReceive(i, j, m)
       \/ /\ i = Recipient
          /\ RecipientReceive(i, j, m)
       \/ /\ i \in Connector
          /\ ConnectorReceive(i, j, m)
       \/ /\ i = Notary
          /\ NotaryReceive(i, j, m)

\* End of message handlers
----
\* Defines how the variables may transition

Termination ==
    /\ \A l \in Ledger : IsFinalLedgerState(ledgerState[l])
    /\ senderState = S_Done
    /\ UNCHANGED vars

Next == \/ Start(Sender)
        \/ NotaryTimeout
        \/ \E l \in Ledger : LedgerAbort(l)
        \/ \E m \in DOMAIN messages : Receive(m)
        \/ Termination

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

=============================================================================
