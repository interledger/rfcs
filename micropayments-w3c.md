# Micropayment Use Cases

Notes from W3C Micropayments Breakout

## Use Cases
- Getting rid of paywalls
- Supporting creative works (tipping?)
- Badges for support
- Premium website experience
- Streaming service payments (electricity, AWS, B2B use cases)
- Ad-free content
- Paying for content curation
- Re-sharing content (getting paid for sharing good content)
- Micro work (like Mechanical Turk)
- IoT
- WebApp monetization
- Paid APIs

## Standard Requirements
1. How small is a micropayment? (Maybe any amount you would be happy to do automatically)
2. Transfer fees would need to be small enough
3. Need to prove why this time is different for micropayments at W3C - the right stakeholders weren’t in the room, implementers all were working on their own projects and not interested in standardization
4. Privacy

## Minutes from IRC

```text
14:07 Stefan: [Demo of browser plug-in]
14:08 Demo is at https://red.ilpdemo.org
14:08 Stefan: Value prop for ILP is that payer and payee don't need to have a common payment method
14:09 ... the demo uses the Interledger Protocol
14:10 Alternate "system" at https://blue.ilpdemo.org
14:10 ... assume I am a content producer
14:10 ... I create content (a website)
14:11 ... video site but the content requires payment
14:12 ... user get's a browser plugin to make payments
14:15 ... the plug-in allows a payment to go through to the content producer
14:15 Evan: What is Interledger?
14:16 ... Stefan showed one of the user experiences that is achievable with micropayments
14:16 ... ILP is one technology to facilitate micropayments
14:17 [ILP slide deck]
14:18 [Video from June workshop of Stefan presenting this deck: https://www.youtube.com/watch?v=zaqWdL25caU&list=PLIR1FI1vEGeHgJeTGOh8CpKXXUhuXJ5Lm]
14:19 ... key problem we are solving is sending payments across networks which solves for reach
14:23 ... in the same way that the IP protocol allows for packets to travel between different underlying networks ILP allows for payments to travel between payment networks
14:25 ... it defines a universal addressing scheme for any asset holding account (bitcoin wallet, bank account, mobile wallet), a way for intermediaries to facilitate the transfer of assets between networks and a way to protect the sender and receiver from intermediaries that might take payment one one network but not deliver the corresponding payment on the next
14:25 network
14:31 alberto: do connectors make money from facilitating payments?
14:31 evan: yes, they can offer a spread
14:32 alberto: I think it is great that this is an open protocol but there is an open question about why we should use this instead of another protocol
14:35 evan: [description of holds and conditional transfers as a way of protecting sender and receiver]
14:35 manu: what is the plan for ILP and the Web Payments WG work.
14:38 AdrianHB: The goal is for there to be one or more payment methods that are based on ILP. Today the Web Payments flow has a step to allow users to pick a payment method our goal is to eliminate that step but the Web Payments work will roll out with that to accommodate the way people pay today.
14:40 ... we see micropayments as a use case that is well suited to solve at W3C using ILP as interop between crypto-currencies.
14:40 topic: Use Cases
14:40 - Content Payments
14:40 (Dropping paywalls)
14:41 @@@: People want to support artists so making it voluntary seems like the thing to do
14:42 evan: you could have a badge system where payments earn you public recognition
14:42 manu: streaming payments - pay as you consume
14:42 ... not just services (removing batches around payments)
14:42 ... realtime payments
14:43 roy: what counts as a micropayment?
14:43 stefan: Def a matter of perspective
14:44 ... either the content provider or the consumer takes the risk on DVP
14:45 ... the smaller the payment the lower the risk
14:45 adamr: the other way to look at it is anything that's not viable because of tx fees
14:46 andrei: -use case - getting rid of ads
14:46 ... if you can pay a site to use it then they don't need ads
14:47 stefan: there is an interesting project from Google called contributor which does this in some respects
14:48 andrei: re-sharing content earns you something
14:49 dimi: -use case - micro work, like mechanical turk
14:50 Internet of Things, like SlockIt where payments are tied to real world
14:50 topic: next steps
14:51 david: This could be done at IG but there is a history of failures in this domain so we'd need to prove that this time is better
14:52 manu: there has been some analysis of the failures and why they happened and it seems like the it was a lack of the right stakeholders
14:53 adrianHB: seems like there is an opportunity here for browsers to differentiate based on their ability to curate content
14:54 stefan: another use case is apps and payment for those
14:55 alberto: do you handle exchange of compliance info
14:55 stefan: we are still just focused on the basic interop layer and those requirements would be met by higher level protocols
14:56 kaoru: privacy vs money laundering is a tough balance. Open standards can be defined that toe that line
15:01 ledger@ietf.org for the IETF mailing list
15:01 public-interledger@w3.org for the W3C mailing list
```
