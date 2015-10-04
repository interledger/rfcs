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
CONSTANTS Ready, Waiting, Done

\* Transfer states
CONSTANTS Proposed, Prepared, Executed, Aborted

\* Message types
CONSTANTS PrepareRequest, ExecuteRequest, PrepareNotify, ExecuteNotify, SubmitReceiptRequest

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
VARIABLE messages

----
\* Sender variables

\* State of the sender (Ready, Waiting, Done)
VARIABLE senderState

\* All sender variables
senderVars == <<senderState>>
----
\* The following variables are all per ledger (functions with domain Ledger)

\* The transfer state (Proposed, Prepared, Executed or Aborted)
VARIABLE transferState

\* All ledger variables
ledgerVars == <<transferState>>
----

\* All variables; used for stuttering (asserting state hasn't changed)
vars == <<messages, senderVars, ledgerVars>>

----
\* Helpers

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = messages (+) SetToBag({m})

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

----
\* Define type specification for all variables

TypeOK == /\ IsABag(messages)
          /\ senderState \in {Ready, Waiting, Done}
          /\ transferState \in [Ledger -> {Proposed, Prepared, Executed, Aborted}]

----
\* Define initial values for all variables

InitSenderVars == /\ senderState = Ready

InitLedgerVars == /\ transferState = [i \in Ledger |-> Proposed]

Init == /\ messages = EmptyBag
        /\ InitSenderVars
        /\ InitLedgerVars

----
\* Define state transitions

\* A participant i asks a ledger j to prepare a transfer
Prepare(i, j) ==
    /\ Send([mtype   |-> PrepareRequest,
             msource |-> i,
             mdest   |-> j])

\* Server i spontaneously requests somebody should execute the transfer - lolwat?
Execute(i, j) ==
    /\ Send([mtype   |-> ExecuteRequest,
             msource |-> i,
             mdest   |-> j])

\* Participant i starts off the chain
Start(i) ==
    /\ senderState = Ready
    /\ senderState' = Waiting
    /\ Prepare(i, i+1)
    /\ UNCHANGED <<ledgerVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a Prepare request from participant j
HandlePrepareRequest(i, j, m) ==
    LET valid == /\ transferState[i] = Proposed
                 /\ j = i - 1
    IN \/ /\ valid
          /\ transferState' = [transferState EXCEPT ![i] = Prepared]
          /\ Reply([mtype   |-> PrepareNotify,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Server i receives an Execute request from server j
HandleExecuteRequest(i, j, m) ==
    LET valid == /\ transferState[i] = Prepared
                 /\ j = Notary
    IN \/ /\ valid
          /\ transferState' = [transferState EXCEPT ![i] = Executed]
          /\ Reply([mtype   |-> ExecuteNotify,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<senderVars>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger j notifies participant i that the transfer is prepared
HandlePrepareNotify(i, j, m) ==
    LET isRecipient == i = Max(Participant)
    IN \/ /\ isRecipient
          /\ Reply([mtype   |-> SubmitReceiptRequest,
                    msource |-> i,
                    mdest   |-> Notary], m)
          /\ UNCHANGED <<senderVars, ledgerVars>>
       \/ /\ \lnot isRecipient
          /\ Reply([mtype   |-> PrepareRequest,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

HandleSubmitReceiptRequest(i, j, m) ==
    \/ /\ i = Notary
       /\ ReplyBroadcast(
            {[mtype    |-> ExecuteRequest,
              msource  |-> i,
              mdest    |-> k] : k \in Ledger}, m)
       /\ UNCHANGED <<senderVars, ledgerVars>>
    \/ /\ i # Notary
       /\ Discard(m)
       /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger j notifies participant i that the transfer is executed
HandleExecuteNotify(i, j, m) ==
    LET isSender == i = Min(Participant)
    IN \/ /\ \lnot isSender
          /\ Reply([mtype   |-> ExecuteRequest,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<senderVars, ledgerVars>>
       \/ /\ isSender
          /\ senderState = Waiting
          /\ senderState' = Done
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars>>
       \/ /\ isSender
          /\ senderState # Waiting
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ /\ m.mtype = PrepareRequest
          /\ HandlePrepareRequest(i, j, m)
       \/ /\ m.mtype = ExecuteRequest
          /\ HandleExecuteRequest(i, j, m)
       \/ /\ m.mtype = PrepareNotify
          /\ HandlePrepareNotify(i, j, m)
       \/ /\ m.mtype = ExecuteNotify
          /\ HandleExecuteNotify(i, j, m)
       \/ /\ m.mtype = SubmitReceiptRequest
          /\ HandleSubmitReceiptRequest(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<senderVars, ledgerVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<senderVars, ledgerVars>>

----
\* Defines how the variables may transition.

Termination == 
    /\ \A l \in Ledger : transferState[l] \in {Executed, Aborted}
    /\ senderState = Done
    /\ UNCHANGED vars 

Next == \/ Start(Min(Participant))
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
