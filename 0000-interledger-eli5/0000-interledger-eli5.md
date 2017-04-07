## Interledger Protocol: Explained Like I'm Five

### Introduction

A _protocol_ is set of rules about how to do something.

The Internet can be seen as a set of rules about how to send messages. For example, when a person follows the rules of the internet to send an email, it can be said that the person is _using the Internet Protocol to transmit information._

An _asset_ is a word meaning anything valuable. For example, money is an asset.

Interledger (aka _ILP_, or _Interledger Protocol_) is a set of rules about how to send assets. For example, when a person follows the rules of Interledger to send money, it can be said that the person is _using the Interledger Protocol to transmit an asset._

Interledger, like the internet, isn't only used by people. It can be used by a computer, a group of computers, or a group of people and/or computers acting together as a company or corporation. The word _party_, whilst sometimes meaning a fun event with music and cake, can also mean a person, a thing, or any group of people or things that can _participate in an action._

The Interledger Protocol has four basic building blocks that are involved together in the action of transmitting an asset from one party to another.

### ILP Building Blocks
- Sender
- Receiver
- Connector
- Ledger

**Senders** want to send an asset to another party. Senders know the amount being sent and to whom. The act of sending something valuable can cost money, so senders are also aware that what arrives could be less than what is sent, and are prepared to accept how much that could be.

**Receivers** are expecting or allowing an asset to arrive from another party. Receivers may know how much to expect, or to expect something to arrive but not how much.  It's also possible receivers may not be expecting anything at all. (Surprise!)

**Connectors** want to connect a sender with a receiver, or many senders with many receivers. Connectors connect directly with senders and receivers, and also with other connectors. This is done to connect as many senders and receivers as possible, through chains of connectors built for each payment.

**Ledgers** are like books that get written in to record how much each sender or receiver has of a particular asset. For example, a ledger for a group of people and their money could record how many dollars each person has. In the real world, an example of a ledger might be a banks list of customers bank accounts and the amount each customer has. A ledger can also be seen to have something like a "ledger manager" that senders, receivers and connectors trust to write changes in the ledger book correctly.

_Note: In a real bank, it's possible for an account to hold multiple types of assets. For example, one bank account could hold amounts in US dollars, Euro's, and Japanese Yen. To keep things simple in the Interledger Protocol, each "ledger" is limited to recording how much different parties have **of exactly the same kind of asset**. If another asset is used by a sender or receiver, another ledger is required for that party. From ILP's point of view, a particular party may have several ledgers associated with them._

### How ILP Works: Trusted & Trustless

When you have an asset stored somewhere, like money in an account at the bank, what do you really have?  The thing you have is the _trust_ that when you go to that place and ask for your thing back, that it will be given to you.  In the case of a bank, you show them your bankcard and ask for your money. Usually that process is automated, you put your card into one of the banks ATM's, tell it you want your money, and out it comes.

If you didn't trust a particular bank to give you your money back when you ask for it, you probably wouldn't give it to them in the first place.

This is important because this idea of trust is at the core of how the pieces of ILP fit together, and - interestingly - how this arrangement enables _trustless payments_.  Let's see how it works:

**Payment Setup: Being Prepared**

As much as possible about an ILP payment is prepared in advance to be sure each party is happy with what's going to happen, and that the funds will remain safe whilst being moved.  It goes like this:

1) A sender asks a connector: "Do you _know and trust_ this receiver?"

2) If the connector knows and trusts the receiver, great.  If not, the connector talks to its "peers" (its "connector friends") to see if any _know and trust_ the receiver, or _know and trust_ another connector that might _know and trust_ the receiver... and so on.  Through this, a "chain of trust" connecting the sender and the receiver is discovered.  This chain may involve just one connector, or it may involve many.

3) Connectors can each charge a little bit for their part in handling the payment.  After the chain is built, the connector closest the sender explains how much the receiver will get if the payment goes down that chain.  If it's much less than what the sender wants to send, the sender will probably choose a different connector.  Therefore, connectors try to make the difference as little as possible whilst still earning something.

4) The sender decides whether or not to use that connector, based on how much it will cost.  If it's a "no", the sender can start over asking a different connector, or asking the same one again (who may figure out a better way this time).  When the sender is happy with the cost, the payment can go ahead.

For each payment, a chain with links of trust is formed between the sender, connector (or connectors) and the receiver.  Each link in the chain trusts the one next to it, but doesn't need to trust any other links in the chain.  What's great about this, is it means the sender and the receiver don't need to trust each other, or even know who each other is - that's what makes ILP payments "trustless".

_[...]_
