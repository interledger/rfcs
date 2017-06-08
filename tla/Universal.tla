------------------------------- MODULE Universal -------------------------------
(***************************************************************************)
(* Formal Specification in TLA^+ of the                                    *)
(* Interledger Protocol Universal (ILP/U)                                  *)
(*                                                                         *)
(*`.                                                                       *)
(* Modeled after the excellent Raft specification by Diego Ongaro.         *)
(*   Available at https://github.com/ongardie/raft.tla                     *)
(*                                                                         *)
(*   Copyright 2014 Diego Ongaro.                                          *)
(*   This work is licensed under the Creative Commons Attribution-4.0      *)
(*   International License https://creativecommons.org/licenses/by/4.0/  .'*)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Bags, TLC

\* The set of ledger IDs
CONSTANTS Ledger

\* The set of participant IDs
CONSTANTS Participant

\* Sender states
CONSTANTS S_Ready, S_ProposalWaiting, S_Waiting, S_Done

\* Connector states
CONSTANTS C_Ready, C_Proposed

\* Ledger states
CONSTANTS L_Proposed, L_Prepared, L_Executed, L_Aborted

\* Message types
CONSTANTS PrepareRequest, ExecuteRequest, AbortRequest,
          PrepareNotify, ExecuteNotify, AbortNotify,
          SubpaymentProposalRequest, SubpaymentProposalResponse

\* Receipt signature
CONSTANTS R_ReceiptSignature

----
\* Global variables

\* Under synchrony we are allowed to have a global clock
VARIABLE clock

\* A bag of records representing requests and responses sent from one process
\* to another
VARIABLE messages

----
\* Sender variables

\* State of the sender (S_Ready, S_Waiting, S_Done)
VARIABLE senderState

\* Whether the sender has received a response from a given connector
VARIABLE senderProposalResponses

\* All sender variables
senderVars == <<senderState, senderProposalResponses>>
----
\* Connector variables

\* State of the connector (C_Ready, C_Proposed)
VARIABLE connectorState

\* All sender variables
connectorVars == <<connectorState>>
----
\* The following variables are all per ledger (functions with domain Ledger)

\* The ledger state (L_Proposed, L_Prepared, L_Executed or L_Aborted)
VARIABLE ledgerState

\* The timeouts for each of the the transfers
VARIABLE ledgerExpiration

\* All ledger variables
ledgerVars == <<ledgerState, ledgerExpiration>>
----

\* All variables; used for stuttering (asserting state hasn't changed)
vars == <<clock, messages, senderVars, connectorVars, ledgerVars>>

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

\* The clock value we expect to be at after the proposal phase
ClockAfterProposal == 2 * Cardinality(Connector) + 2

\* The clock value we expect after the preparation phase
ClockAfterPrepare == ClockAfterProposal + 2 * Cardinality(Ledger) + 1

\* The clock value we expect to be at after the execution phase
ClockAfterExecution == ClockAfterPrepare + 2 * Cardinality(Ledger) + 1
----
\* Define type specification for all variables

TypeOK == /\ clock \in Nat
          /\ IsABag(messages)
          /\ senderState \in {S_Ready, S_ProposalWaiting, S_Waiting, S_Done}
          /\ senderProposalResponses \in [Connector -> BOOLEAN]
          /\ connectorState \in [Connector -> {C_Ready, C_Proposed}] 
          /\ ledgerState \in [Ledger -> {L_Proposed, L_Prepared, L_Executed, L_Aborted}]
          /\ ledgerExpiration \in [Ledger -> Nat]

Consistency ==
    \A l1, l2 \in Ledger : \lnot /\ ledgerState[l1] = L_Aborted
                                 /\ ledgerState[l2] = L_Executed

Inv == /\ TypeOK
       /\ Consistency

----
\* Define initial values for all variables

InitSenderVars == /\ senderState = S_Ready
                  /\ senderProposalResponses = [i \in Connector |-> FALSE]

InitConnectorVars == connectorState = [i \in Connector |-> C_Ready]

InitLedgerVars == /\ ledgerState = [i \in Ledger |-> L_Proposed]
                  /\ ledgerExpiration = [i \in Ledger |-> ClockAfterExecution - i]

Init == /\ clock = 0
        /\ messages = EmptyBag
        /\ InitSenderVars
        /\ InitConnectorVars
        /\ InitLedgerVars

----
\* Define state transitions

\* Participant i proposes all the subpayments
StartProposalPhase(i) ==
    /\ senderState = S_Ready
    /\ senderState' = S_ProposalWaiting
    /\ Broadcast({[
         mtype    |-> SubpaymentProposalRequest,
         msource  |-> i,
         mdest    |-> k
       ] : k \in Connector})
    /\ UNCHANGED <<ledgerVars, connectorVars, senderProposalResponses>>

\* Participant i starts off the preparation chain
StartPreparationPhase(i) ==
    /\ senderState = S_ProposalWaiting
    /\ \E p \in DOMAIN senderProposalResponses : senderProposalResponses[p]
    /\ senderState' = S_Waiting
    /\ Send([mtype   |-> PrepareRequest,
             msource |-> i,
             mdest   |-> i+1])
    /\ UNCHANGED <<ledgerVars, connectorVars, senderProposalResponses>>

\* Ledger spontaneously aborts
LedgerAbort(l) ==
    /\ ledgerState[l] = L_Proposed
    /\ ledgerState' = [ledgerState EXCEPT ![l] = L_Aborted]
    /\ Send([mtype   |-> AbortNotify,
             msource |-> l,
             mdest   |-> l-1])
    /\ UNCHANGED <<senderVars, connectorVars, ledgerExpiration>>

\* Transfer times out
LedgerTimeout(l) ==
    /\ \lnot IsFinalLedgerState(ledgerState[l])
    /\ ledgerExpiration[l] =< clock
    /\ ledgerState' = [ledgerState EXCEPT ![l] = L_Aborted]
    /\ Send([mtype   |-> AbortNotify,
             msource |-> l,
             mdest   |-> l-1])
    /\ UNCHANGED <<senderVars, connectorVars, ledgerExpiration>>

\* If no messages are in flight and the sender isn't doing anything, advance the
\* clock
NothingHappens ==
    /\ clock \leq Max({ledgerExpiration[x] : x \in Ledger})
    /\ BagCardinality(messages) = 0
    /\ senderState # S_Ready
    /\ \/ senderState # S_ProposalWaiting
       \/ \A p \in DOMAIN senderProposalResponses : \lnot senderProposalResponses[p]
    /\ UNCHANGED <<messages, senderVars, connectorVars, ledgerVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Ledger i receives a Prepare request from participant j
LedgerHandlePrepareRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Proposed
                 /\ j = i - 1
    IN \/ /\ valid
          /\ i \in Ledger
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Prepared]
          /\ Reply([mtype   |-> PrepareNotify,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars, connectorVars, ledgerExpiration>>
       \/ /\ \lnot valid
          /\ i \in Ledger
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Ledger i receives an Execute request from process j
LedgerHandleExecuteRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Prepared
                 /\ ledgerExpiration[i] > clock
                 /\ m.mreceipt = R_ReceiptSignature
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Executed]
          /\ Reply([mtype    |-> ExecuteNotify,
                    msource  |-> i,
                    mdest    |-> i-1,
                    mreceipt |-> m.mreceipt], m)
          /\ UNCHANGED <<senderVars, connectorVars, ledgerExpiration>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Ledger i receives a message
LedgerReceive(i, j, m) ==
    \/ /\ m.mtype = PrepareRequest
       /\ LedgerHandlePrepareRequest(i, j, m)
    \/ /\ m.mtype = ExecuteRequest
       /\ LedgerHandleExecuteRequest(i, j, m)

\* Sender receives a SubpaymentProposal request
SenderHandleSubpaymentProposalResponse(i, j, m) ==
    /\ i = Sender
    /\ senderProposalResponses' = [senderProposalResponses EXCEPT ![j] = TRUE]
    /\ Discard(m)
    /\ UNCHANGED <<connectorVars, ledgerVars, senderState>>

\* Ledger j notifies sender that the transfer is executed
SenderHandleExecuteNotify(i, j, m) ==
    \/ /\ senderState = S_Waiting
       /\ senderState' = S_Done
       /\ Discard(m)
       /\ UNCHANGED <<ledgerVars, connectorVars, senderProposalResponses>>
    \/ /\ senderState # S_Waiting
       /\ Discard(m)
       /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Ledger j notifies sender that the transfer is aborted
SenderHandleAbortNotify(i, j, m) ==
    LET isSenderWaiting == senderState \in { S_ProposalWaiting, S_Waiting, S_Ready }
    IN \/ /\ isSenderWaiting
          /\ senderState' = S_Done
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars, connectorVars, senderProposalResponses>>
       \/ /\ \lnot isSenderWaiting
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Sender receives a message
SenderReceive(i, j, m) ==
    \/ /\ m.mtype = SubpaymentProposalResponse
       /\ SenderHandleSubpaymentProposalResponse(i, j, m)
    \/ /\ m.mtype = ExecuteNotify
       /\ SenderHandleExecuteNotify(i, j, m)
    \/ /\ m.mtype = AbortNotify
       /\ SenderHandleAbortNotify(i, j, m)

\* Ledger j notifies recipient that the transfer is prepared
RecipientHandlePrepareNotify(i, j, m) ==
    \/ /\ Reply([mtype    |-> ExecuteRequest,
                 msource  |-> i,
                 mdest    |-> i-1,
                 mreceipt |-> R_ReceiptSignature], m)
       /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Recipient receives a message
RecipientReceive(i, j, m) ==
    \/ /\ m.mtype = PrepareNotify
       /\ RecipientHandlePrepareNotify(i, j, m)

\* Connector i receives a SubpaymentProposal request
ConnectorHandleSubpaymentProposalRequest(i, j, m) ==
    /\ connectorState' = [connectorState EXCEPT ![i] = C_Proposed]
    /\ Reply([mtype    |-> SubpaymentProposalResponse,
              msource  |-> i,
              mdest    |-> j], m)
    /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger j notifies connector i that the transfer is prepared
ConnectorHandlePrepareNotify(i, j, m) ==
    \/ /\ Reply([mtype   |-> PrepareRequest,
                 msource |-> i,
                 mdest   |-> i+1], m)
       /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Ledger j notifies connector i that the transfer is executed
ConnectorHandleExecuteNotify(i, j, m) ==
    /\ Reply([mtype    |-> ExecuteRequest,
              msource  |-> i,
              mdest    |-> i-1,
              mreceipt |-> m.mreceipt], m)
    /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Ledger j notifies connector i that the transfer is aborted
ConnectorHandleAbortNotify(i, j, m) ==
    /\ Discard(m)
    /\ UNCHANGED <<senderVars, connectorVars, ledgerVars>>

\* Connector receives a message
ConnectorReceive(i, j, m) ==
    \/ /\ m.mtype = SubpaymentProposalRequest
       /\ ConnectorHandleSubpaymentProposalRequest(i, j, m)
    \/ /\ m.mtype = PrepareNotify
       /\ ConnectorHandlePrepareNotify(i, j, m)
    \/ /\ m.mtype = ExecuteNotify
       /\ ConnectorHandleExecuteNotify(i, j, m)
    \/ /\ m.mtype = AbortNotify
       /\ ConnectorHandleAbortNotify(i, j, m)

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

\* End of message handlers
----
\* Defines how the variables may transition

Termination ==
    /\ \A l \in Ledger : IsFinalLedgerState(ledgerState[l])
    /\ senderState = S_Done
    /\ UNCHANGED vars

Next == \/ /\ \/ StartProposalPhase(Sender)
              \/ StartPreparationPhase(Sender)
              \/ \E l \in Ledger : LedgerAbort(l)
              \/ \E l \in Ledger : LedgerTimeout(l)
              \/ \E m \in DOMAIN messages : Receive(m)
              \/ NothingHappens
           /\ clock' = clock + 1
        \/ Termination

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

=============================================================================
