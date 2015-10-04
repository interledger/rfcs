------------------------------- MODULE Atomic -------------------------------
(***************************************************************************)
(* Formal Specification in TLA^+ of the                                    *)
(* Interledger Protocol Atomic (ILP/A)                                     *)
(*                                                                         *)
(*`.                                                                       *)
(* Copyright 2015 Ripple Labs.                                             *)
(*    This work is licensed under the Creative Commons Attribution-4.0     *)
(*    International License https://creativecommons.org/licenses/by/4.0/   *)
(*                                                                         *)
(* Modeled after the excellent Raft specification by Diego Ongaro.         *)
(*   Available at `\href{https://github.com/ongardie/raft.tla}{Test}'      *)
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

\* Ledger states
CONSTANTS L_Proposed, L_Prepared, L_Executed, L_Aborted

\* Message types
CONSTANTS PrepareRequest, ExecuteRequest, AbortRequest, PrepareNotify, ExecuteNotify, AbortNotify, SubmitReceiptRequest

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
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

\* Remove a message from the bag of messages. Used when a server is done
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

----
\* Define type specification for all variables

TypeOK == /\ IsABag(messages)
          /\ senderState \in {S_Ready, S_Waiting, S_Done}
          /\ ledgerState \in [Ledger -> {L_Proposed, L_Prepared, L_Executed, L_Aborted}]

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
    /\ Send([mtype   |-> PrepareRequest,
             msource |-> i,
             mdest   |-> i+1])
    /\ UNCHANGED <<ledgerVars, notaryVars>>

\* Notary times out
NotaryTimeout ==
    /\ notaryState = N_Waiting
    /\ notaryState' = N_Aborted
    /\ Broadcast(
            {[mtype    |-> AbortRequest,
              msource  |-> Notary,
              mdest    |-> k] : k \in Ledger})
    /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger spontaneously aborts
LedgerAbort(l) ==
    /\ ledgerState[l] = L_Proposed
    /\ ledgerState' = [ledgerState EXCEPT ![l] = L_Aborted]
    /\ Send([mtype   |-> AbortNotify,
             msource |-> l,
             mdest   |-> l-1])
    /\ UNCHANGED <<senderVars, notaryVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a Prepare request from participant j
HandlePrepareRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Proposed
                 /\ j = i - 1
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Prepared]
          /\ Reply([mtype   |-> PrepareNotify,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars, notaryVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Server i receives an Execute request from server j
HandleExecuteRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Prepared
                 /\ j = Notary
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Executed]
          /\ Reply([mtype   |-> ExecuteNotify,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<senderVars, notaryVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Server i receives an Abort request from server j
HandleAbortRequest(i, j, m) ==
    LET valid == /\ \/ ledgerState[i] = L_Proposed
                    \/ ledgerState[i] = L_Prepared
                 /\ j = Notary
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Aborted]
          /\ Reply([mtype   |-> AbortNotify,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<senderVars, notaryVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger j notifies participant i that the transfer is prepared
HandlePrepareNotify(i, j, m) ==
    LET isRecipient == i = Max(Participant)
    IN \/ /\ isRecipient
          /\ Reply([mtype   |-> SubmitReceiptRequest,
                    msource |-> i,
                    mdest   |-> Notary], m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>
       \/ /\ \lnot isRecipient
          /\ Reply([mtype   |-> PrepareRequest,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger j notifies participant i that the transfer is executed
HandleExecuteNotify(i, j, m) ==
    LET isSender == i = Min(Participant)
    IN \/ /\ \lnot isSender
          /\ Reply([mtype   |-> ExecuteRequest,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>
       \/ /\ isSender
          /\ senderState = S_Waiting
          /\ senderState' = S_Done
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars, notaryVars>>
       \/ /\ isSender
          /\ senderState # S_Waiting
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Ledger j notifies participant i that the transfer is aborted
HandleAbortNotify(i, j, m) ==
    LET isSenderAndWaiting == /\ i = Min(Participant)
                              /\ \/ senderState = S_Waiting
                                 \/ senderState = S_Ready
    IN \/ /\ isSenderAndWaiting
          /\ senderState' = S_Done
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars, notaryVars>>
       \/ /\ \lnot isSenderAndWaiting
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Notary receives a signed receipt
HandleSubmitReceiptRequest(i, j, m) ==
    \/ /\ i = Notary
       /\ notaryState = N_Waiting
       /\ notaryState = N_Committed
       /\ ReplyBroadcast(
            {[mtype    |-> ExecuteRequest,
              msource  |-> i,
              mdest    |-> k] : k \in Ledger}, m)
       /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>
    \/ /\ \/ i # Notary
          \/ notaryState # N_Waiting
       /\ Discard(m)
       /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ /\ m.mtype = PrepareRequest
          /\ HandlePrepareRequest(i, j, m)
       \/ /\ m.mtype = ExecuteRequest
          /\ HandleExecuteRequest(i, j, m)
       \/ /\ m.mtype = AbortRequest
          /\ HandleAbortRequest(i, j, m)
       \/ /\ m.mtype = PrepareNotify
          /\ HandlePrepareNotify(i, j, m)
       \/ /\ m.mtype = ExecuteNotify
          /\ HandleExecuteNotify(i, j, m)
       \/ /\ m.mtype = AbortNotify
          /\ HandleAbortNotify(i, j, m)
       \/ /\ m.mtype = SubmitReceiptRequest
          /\ HandleSubmitReceiptRequest(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<senderVars, ledgerVars, notaryVars>>

----
\* Defines how the variables may transition.

Termination == 
    /\ \A l \in Ledger : IsFinalLedgerState(ledgerState[l])
    /\ senderState = S_Done
    /\ UNCHANGED vars

Consistency ==
    \A l1, l2 \in Ledger : \lnot /\ ledgerState[l1] = L_Aborted
                                 /\ ledgerState[l2] = L_Executed

Next == \/ Start(Min(Participant))
        \/ NotaryTimeout
        \/ \E l \in Ledger : LedgerAbort(l)
        \/ \E m \in DOMAIN messages : Receive(m)
\*        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN messages : DropMessage(m)
        \/ Termination

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* The spec should be type-safe
THEOREM Spec => []TypeOK

=============================================================================
