---
title: Interledger Protocol - Explain Like I'm Five (ELI5)
draft: 1
---
## Interledger Protocol: Explain Like I'm Five (ELI5)

### Introduction

A _protocol_ is set of rules about how to do something.

The Internet can be seen as a set of rules about how to send messages. For example, when a person follows the rules of the Internet to send an email, it can be said that the person is _using the Internet Protocol to transmit information._

An _asset_ is a word meaning anything valuable. For example, money is an asset.

Interledger (aka _Interledger Protocol_, or _ILP_) is a set of rules about how to send assets. For example, when a person follows the rules of the Interledger to send money, it can be said that the person is _using the Interledger Protocol to transmit an asset._

Interledger, like the Internet, isn't only used by people. It can be used by a computer, a group of computers, or a group of people and/or computers acting together as a company or corporation. The word _party_ is sometimes used to describe a person, thing, or any group of people or things that can _participate in an action._

The Interledger Protocol has four basic building blocks that participate together in the action of transmitting an asset from one party to another.

These building blocks - described in the next section - were created to fit together in enough ways to transmit an asset of any kind, through any system or systems, anywhere in the world, and handle any necessary exchanges of asset type along the way.

What the Internet did for information, Interledger aims to do for value.

_(Key point: There are many kinds of assets, even within an asset group such as "money".  For example, US Dollars, Japanese Yen and Mexican Peso's are all different kinds of money.  Gold and Silver are different kinds of "precious metals" - another asset group. There are also many systems to keep track of who owns what asset, and to handle exchanges of one kind of asset for another.  The problem is, the systems don't always connect to each other very well, if they connect at all.  It can be difficult, costly and time-consuming to send value around the world at the present time.  ILP makes it easy, cost-effective and fast.)_

### ILP Basics: Building Blocks

- Sender
- Receiver
- Connector
- Ledger

**Senders** want to send an asset to a particular receiver. Senders know the amount being sent and to whom. Sending something valuable can cost money, and in ILP this cost may be subtracted from the asset amount as it is transmitted.  So, senders are aware that what arrives could be less than what is sent, and are prepared for how much that could be.

**Receivers** are expecting or allowing an asset to arrive from a particular sender. Receivers may know how much to expect, or to expect something to arrive and from whom, but not how much.

**Connectors** want to link senders with receivers to make ILP payments possible. Connectors also link up with other connectors. This is done to connect as many senders with receivers as possible, through chains of connectors that are built for each payment.

**Ledgers** are like books that get written in to record how much of a particular asset different parties have. For example, a ledger for a group of people and their money could record how many dollars each person has. In the real world, an example of a ledger might be a banks list of customers bank accounts and the amount each customer has. A ledger also has something like a "ledger manager" that senders, receivers and connectors trust to write changes in the ledger book correctly. If a sender and receiver are on the same ledger, the sender can make an ILP payment to the receiver without a connector's help.

_Note: In a real bank, it's possible for an account to hold multiple types of assets. For example, one bank account could hold amounts in US dollars, Euro's, and Japanese Yen. To keep things simple in the Interledger Protocol, each "ledger" is limited to recording how much different parties have **of exactly the same kind of asset**. If another asset is used by a sender or receiver, another ledger is kept for that asset. From ILP's point of view, a particular party may have several ledgers associated with them._

### ILP Security: Trusted & Trustless

When you have an asset stored somewhere, like money in a bank, what do you really have?  The thing you really have is _trust_ that when you go to that place and ask for your asset back, that it will be given to you.  In the case of a bank, you show them your bankcard and ask for your money.  Usually that process is automated: you put your card into a bank ATM, tell it how much you want, and out it comes.

If you didn't trust a particular bank to give you your money back when you ask for it, you probably wouldn't give it to them in the first place.

This is important because this idea of trust is at the core of how the pieces of ILP fit together, and - interestingly - how this arrangement enables _trustless payments_.  Let's see how it works:

**Payment Quotes: Where To & How Much?**

As much as possible about an ILP payment is worked out in advance to be sure each party is happy with what's going to happen, and that the funds will remain safe while in transition.  While it's possible for a sender to make a payment to a receiver on the same ledger, examining that scenario won't involve much of what makes ILP interesting.  So let's take the example that the sender and receiver are on different ledgers.

Before the payment is made, the sender needs to be happy with how much the payment will cost. The process, called _quoting_, goes like this:

1) First, a sender asks a connector: "Do you know this receiver?"

2) If the connector knows the receiver, great.  If not, the connector talks to its "peers" (its "connector friends") to see if any know the receiver, or know another connector that might know the receiver... and so on.  Through this process, a chain of connectors linking the sender to the receiver is discovered.  This chain may involve just one connector, or it may involve many.

3) Connectors can each charge a little bit for their part in handling the payment.  After the chain is built, the connector closest the sender explains how much the receiver will get if the payment goes down that chain.  That is, the connector gives the sender a _quote_. If it's much less than what the sender wants to send, the sender will probably choose a different connector.  So connectors try make the cost to the sender as little as possible, while still earning something.

4) The sender decides whether or not to use that connector, based on how much it will cost.  If it's a "no", the sender can start over asking a different connector, or asking the same one again (who may figure out a way to make it cheaper this time).  When the sender is happy with the cost, the payment can go ahead.

For each payment, a chain with links of trust is formed between the sender, connector - or connectors - and the receiver.  Each link in the chain trusts the one before it not to waste its time, but no link needs to trust any other links in the chain or even know about them.  What's great about this, is it means the sender and the receiver don't need to trust each other, or even know who each other is.

_Key point: If a sender makes a payment with ILP, it is assured that either the receiver will receive the amount the sender agreed to, or the sender will get their original amount returned.  The sender doesn't need to trust anyone in-between, and the receiver can be sure the sender agreed to the transfer (and so won't later try get the asset back).  This is what makes ILP payments "trustless"._

**Payment Security**

Even with all this worked out, there are still a couple of things that could go wrong.  For example, what happens if a connector lies about how much the payment will cost?  It's unlikely, but if it did happen, ILP guarantees the sender will get their original asset back in their account.  Then of course, the sender could try sending again a different way.  In a small number of cases, this situation may result in a connector losing money.  That's why connectors charge a little bit for making payments, and it's also why they want to choose carefully to link up with ledgers they can trust.  Also, if a connector did lie, all connectors will know about it and "unfriend" them to make it difficult for that connector to be involved in an ILP payment again.

Much of what happens throughout an ILP payment is actually only there to protect the asset from exactly this kind of thing during its transition from one ledger to another.  One of the main techniques used is called a _cryptographic condition_.  This is a complex topic, so we're going to use an analogy to represent it.  Instead of a "cryptographic condition", let's call it a _special box._

*The Special Box*

Before a payment can happen, the sender and the receiver have a private talk, and decide that its ok if the sender sends an asset to the receiver using ILP at some future time.  When the payment happens, it may go through many connectors that the sender doesn't know or trust, and the sender wants to be sure the asset arrives safely with the receiver and nobody else.  To help with this, the sender and receiver come up with a secret password, write it down a few times on some pieces of paper, and put each one in a special box.  These special boxes are impossible to open, or to see inside.  But, there is a slit in the top anyone can insert a piece of paper with a password written on it.  If the password is the same as the original, the box opens.  If not, the box stays closed.  The sender passes a few of these special boxes to their ledger manager, who takes one of the boxes and hands the rest along.  Every party involved in the payment will take one and use it to make sure everything is going according to plan.

_Key point: even though all parties will have special boxes after the payment is prepared, none of the parties but the sender and the receiver will have the password, nor anything valuable that could be taken advantage of.  The is important because it means at this point, the payment can be backed-out-of, without any risk to any party of their assets.  When a payment is prepared, but before it actually goes ahead, the special boxes don't give the various parties any power over the assets involved.  The special boxes only give the various parties the **ability to check a password is correct.**_

### How ILP Works: An Example Payment

Let's imagine someone wants to send $10 US Dollars (USD) from their US bank account, to their friend's bank account in Japan.  In this case, the person in the US is the sender, and their friend in Japan is the receiver.  The problem is the friends Japanese bank won't accept USD, it only accepts Japanese Yen (JPY).  What to do?

This is where the connector comes in.  The connector has an account for USD at the same bank as the sender.  So from ILP's point of view, _the connector and the sender have accounts on the same ledger._

That same connector also happens to have an account for JPY at the same bank as the receiver.  So from ILP's point of view _the connector and the receiver have accounts on the same ledger._

If a connector has accounts on the same ledger as the sender and the receiver, an ILP payment involving the connector is now possible.

Let's say the connector offered the sender a price of ¥105 Japanese Yen for each $1 USD, and the sender was happy with that price.  That would mean the sender would send $10 USD, and the receiver would receive ¥1050 JPY (¥105 x $10 = ¥1050).

Here's what happens next:

1) The sender says to the ledger manager of the USD ledger:

- "I've decided to send $10 USD. Can you write in the ledger book that its not in my account anymore?"
- "Then, can you write that this $10 is in the ledgers special 'holding' account?"
- "Also, here's four special boxes.  Keep one, and give the other three to this connector."
- "Finally, tell the connector if they give you a password that opens this box, you'll erase the entry in the holding account, and record instead that the $10 USD is in the connectors account!"

2) The USD ledger manager erases $10 USD from the senders account, puts $10 USD in the holding account, tells the connector about everything, keeps a box, and gives the connector the other two boxes.  Now, its the connectors turn to do a similar thing on the JPY ledger.  The connector says to the JPY ledger manager:

- "I'm going to give someone on your ledger ¥1050 JPY.  Can you take ¥1050 from my account, and put it in the special 'holding' account?
- "Then, can you take these boxes, keep one, and give the other to the receiver?"
- "Finally, wait for a password from the receiver - if the password opens your box, put the ¥1050 in the receivers account, tell the receiver you've done that, and let me know too!"

3) The JPY ledger manager does all this, and gives the receiver the last box.  The receiver hears all about the payment and puts the password they previously arranged with the sender into the box.  The box opens!  So, the receiver knows this box came from the sender, and that this payment is a real payment the sender wants to make.  The receiver also knows that right now, some Japanese Yen are on hold for the receiver in the JPY ledger, waiting for this password.  The receiver wants the money, and trusts the JPY ledger manager.  At this point, what the receiver does determines whether the payment goes ahead or not.  This is called the payment "executing".  The receiver now causes the payment to execute, by giving the password to the JPY ledger manager.

4) The JPY ledger manager puts this password from the receiver into the box, and it opens! The JPY ledger manager changes the entries in the ledger, so that the holding account doesn't have the ¥1050 JPY, and the receiver's account has it instead.  The ledger manager then tells the connector what happened, and hands this password on to them.

5) The connector tries the password in the box, and of course - it opens.  The connector now knows this password will open the box the USD ledger manager has, and the ledger manager will put $10 USD into the connector's account on the USD ledger.  The connector trusts the USD ledger manager, and so hands the password on to them.

6) The USD ledger manager tries the password and when the box opens, puts the USD from the holding account into the connectors account.

So how are things now?  The sender has no USD, that's good - those USD were meant to be sent away.  The receiver has ¥1050 JPY.  That's good, that's just what the sender wanted.  The payment is complete!

_Note: The connector now has $10 USD, and no JPY. But that connector could wait to be contacted by another sender, this time one from Japan, who wants to send JPY to the US.  The connector could then offer $1 USD for, say, ¥109 JPY each.  When that payment is done, the connector will have ¥1090 JPY on the JPY ledger, a little bit more than the ¥1050 the connector had before the first payment.  That's one way connectors can earn money by linking senders and receviers on the Interledger._

### The Magic of ILP: Payments Are An Illusion

Something interesting about all of this, is that on the Interledger, it may well be correct to say that no assets are actually ever "sent" anywhere.  What actually happens is the various ledger managers involved all agree to write in their ledger books at about the same time.  What's written first is that the asset is _not_ in the senders account, and then that it _is_ in the sending ledgers holding account.  Then its written that the asset is _not_ in the connectors account, but _is_ in the receiving ledgers holding account.  When the password is received, the ledger managers do the same thing, but from the receiving ledgers holding account to the receivers account, and the sending ledgers holding account, to the connectors account.  Assets are appearing and disappearing _locally_ on different ledgers, and because this is happening at about the same time, and because everyone involved is happy with what's happening, it creates the effect of an asset _seeming_ to be sent from the sender's account to the receivers account, and maybe changing form along the way.  But really, that's an illusion.

_Note: The reason for the "holding" part is that it protects the assets.  If anything goes wrong with the payment while the assets are on hold - for example, if the receiver rejects the payment - the assets can simply be taken from the holding accounts and put back into the accounts they came from.  In fact, in the case of the example given, if the receiver rejected the payment the assets would **have** to be put back.  This is because if the receiver rejected the payment, no password would have been given that could open the boxes, so none of the ledger managers would have done anything._

**Asset Exchange & Connectors**

What's particularly useful about about ILP payments, is that the _kind_ of asset being sent doesn't need to be the same kind as the asset that is received.  The asset kind may be exchanged a few times during a payment.

In the example above, if there wasn't a convenient connector available for USD and JPY, the payment could have involved two or more connectors.  For example, the first connector could be happy to gain US Dollars on the senders ledger, and provide Mexican Peso's on another ledger.  A second connector may be happy to gain some Mexican Peso's on the first connectors ledger, and lose some Japanese Yen on the receivers ledger.  In this case the payment would have involved seven parties acting together.  One sender, two connectors, one receiver and three ledgers.

When looked at this way, each connector could also be seen as just another sender, and in truth, given the way ILP works under the hood - it's a little like that.

### Further Reading & What You Didn't Know You Know

We've taken an elementary look at ILP and how it works.  In the course of this document, we've skipped over some complex terms commonly used to describe ILP, but we haven't skipped over basic functionality or the principles at work.

Hopefully, with what you know now, you'll be able to more readily comprehend other ILP documentation, based on a firm understanding of the basic principles.  What you may not realise is just how much you know already:

**What's Really In The Special Box?**

The "special box" was used as an analogy for a "cryptographic condition".  If you read about these elsewhere in the ILP documentation, you might find them associated with the terms "pre-image", "digest", "hash", "fulfillment" and if those weren't frightening enough, "SHA-256".

But you actually already know what most of these mean.  The "cryptographic condition" is the whole arrangement of the box, its hidden password and the checking a password matches the one inside.  The "pre-image" is just another word for the password.  The "digest", or "hash" is a kind of mushed-up version of that password.  Checking for a "valid pre-image of the hash", is the same as checking "the password matches the one in the box", and if it does match, "fulfilling the condition".  Finally, "SHA-256" is just a fancy name for a particular type of special box that may be used in ILP.  There are many types of these special boxes that all do almost the same thing, and they all have scary names.  Don't let it discourage you!
