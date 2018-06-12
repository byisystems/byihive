# byihive
This is the byihive project by [BYI Systems](https://byisystems.com) . 

It is based on RFC3506 - Requirements and Design for Voucher Trading System (VTS)
You can find out more about RFC3506 here: https://tools.ietf.org/rfc/rfc3506.txt

The byihive project aims to bring peer to peer transactability to everyone.

Our goal is to bring out a reference implementation in erlang (see ["Why Erlang"] below) so that anyone can use it in their applications.

Applications of byihive include:
 - Creating your own peer to peer ledger system - similar to splitwise, but no splitwise to track you.
 - Creating your own local currency system without a centralised ledger tracking everything.
 - Creating your own loyalty points system.
 
Here's our timeline:
 - End of Q2 2018 - we release the first erlang draft code which is capable of managing a complete voucher life cycle.
 - End of Q3 2018 - we release the first reference API which is usable for local currency communities to implement their own apps.
 
### Why Erlang

According to Wikipedia, Erlang has the following properties:

"
The Erlang runtime system is known for its designs that are well suited for systems with the following characteristics:
    - Distributed
    - Fault-tolerant
    - Soft real-time,
    - Highly available, non-stop applications
    - Hot swapping, where code can be changed without stopping a system.[4]
"

As you can imagine, these are very attractive properties for any system that is as critical as one involves people transacting with each other. We found that Erlang had been used in critical communications infrastructure, and is seasoned and proven. 


We use formal specification methods to design byihive. The first reference spec in TLA+ is released here as a one-off.
See the [specifications](/specifications/) directory to have a look.

Here too, Erlang proved to be attractive, as our specs naturally mapped to the code, allowing for a very robust design/implementation methodology. Wikipedia says:

"
The Erlang programming language is known for the following properties:[5]
    - Immutable data
    - Pattern matching
    - Functional programming
"
