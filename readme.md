# Twovar

Assorted variants of twophase commit, modeled in TLA+. These are manually defined examples designed to illustrate different environmental variations that may impact robustness.

## Motivation

This repository is tests the notion of software robustness. While formally defined in *A behavioral notion of robustness for software systems, by Zhang et al*, (https://eskang.github.io/assets/papers/fse20-robustness.pdf), robustness can be described (imprecisely) as the number of *environmental* variations a system can tolerate while still satisfying its properties.

A system's *environment* is all of the external factors that influence it -- for instance, human users, or unreliable networks. A good system should be able to tolerate some deviations from expected behavior -- for instance, a user accidentally pressing the wrong button -- while still working.

So we evaluate robustness by finding all the variations a system can tolerate!

### Twophase Commit
In our case, we consider the twophase commit protocol for atomic commitment. 

Twophase commit can be decomposed into three logical entities:
1. The transaction manager
2. The resource managers
3. The environment both entities interact with while passing messages. This can be though of as the network.

### The Robustness Question

So the network is our environment. What sort of variations might a network have?

What if it's an unreliable network that drops packets?

What if a malicious actor sends erroneous messages to the system?

These are the kind of environmental variations we seek to evaluate!

## The Model

Our model decomposes to three entities, as described above
1. The transaction manager
2. The resource managers
3. The network environment.

The base model is defined in TwoPhase.tla and is derived from https://github.com/cmu-soda/recomp-verify.

Here is an example of an allowed behavior in the normative environment E:

1. The system starts out with the transaction manager in the *init* state and all resource managers in the *working* state. The set of messages sent is the empty set.
2. Each resource manager broadcasts a "prepared" message and sets its own state to "prepared".
3. Reading from the message set, the transaction manager adds each resource manager to its internal set of prepared resource managers.
4. Noticing that all resource managers are prepared, the transaction manager broadcasts a commit message.
5. The transaction manager sets its state to committed.
6. Each resource manager reads the commit message and sets its own state to committed. 

If a resource manager aborts, it will not broadcast a "prepared" message, and so the transaction manager will not commit

## Project Structure
* base:
	* This contains the base configuration and twophase model.
* variations:
	* This contains the versions of the protocol with modified environments.
* mc_variations:
	* Some models are infinite state and so can't be checked by TLC in finite time. This directory contains the finite-state versions of those models.
* decomps:
    * Using CMU SoDA's recomp-verify (https://github.com/cmu-soda/recomp-verify), these variations have been decomposed. Special effort has been put in to making these decompositions as similar to each other as possible, including adding in some redundant checks, so that diffs will be easily viewed.
    * Note: since decompositions are manually copied (TODO: make script doing this!), there is a possibility that some are out of date. 

## Variations

### Message Queue

#### Files:
* mc_variations/MCTwoPhaseQueue.tla
* variations/TwoPhaseQueue.tla

#### Description:

The base model uses a set as the messages data structure. Since elements are not removed from the set, this is comparable to broadcasting every message. 

Acknowledging the classic networking message queue, we rebuilt messages to use a queue instead of a set. Now all communication is point-to-point!

Items are then removed from the queue as they're received. To enable this, we modified messages to include a specific destination and changed the system entities to dequeue messages addressed to them.

Note as well that since the commit message is no longer broadcasted, it must be sent to each entity. However, because of the nature of the original system's design and TLA+, we got this change more or less for free. Once the transaction manager enters the commit state, it will maintain transitions to the SndCommit message for each resource manager.

##### MC Finite state:
In the message queue model, messages can be infinitely enqueued without ever being received. For instance, the transaction manager can continuously send commit messages without giving their targets a chance to read them!

Since these are value distinct states, TLA will attempt to evaluate all of them.

To fix this issue, I:
1. Set a maximum queue length of three.
2. Allowed senders to see if their messages were recieved (i.e. the recipient's state changed). This emulates acknowledgement messages.

#### A note:
Run this with -deadlock -- if all managers abort, no transitions save stuttering steps will remain!

### Message Removed From Set
#### Files:
- variations/TwoPhaseMsgRemoved.tla

#### Description
In this variation, messages are removed from the set of all messages as they're read. Like with the message queue, this emulates point to point communication, but unlike with the message queue, this imposes no additional ordering requirements. 

Getting the message removed variant to work required adding destination metadata, as in the message queue.

### Malicious Messages

#### Files:
- variations/TwoPhaseMalicious.tla

#### Description:
This variation allows erroneous "prepared" messages to be sent to the transaction manager.

As soon as the transaction manager receives a prepared message, it assumes that the transaction manager is permanently prepared. Therefore, erroneous messages break the system!

### No Messages

#### Files:
- variations/TwoPhaseNoMsg.tla

#### Description:
This variation maintains no data structure for the messages at all! 

The system as designed reads from the message set as an enabling condition for all receive message states. So removing this data structure also removes these enabling conditions, breaking the system.

### Live Queue

#### Files:
- variations/TwoPhaseQueueLive.tla
- variations/TwoPhaseLive.cfg
- mc_variations/MCTwoPhaseQueueLive.tla
- mc_variations/TwoPhaseLive.cfg

#### Description:
In this variation, as opposed to the *consistent* safety property used in the other models, an additional *liveness* property is added stating that, eventually, all resource managers will either be committed or aborted.

By default, TLC makes no fairness guarantees. A model can easily take infinite stuttering steps (perhaps emulating a crash), so this condition fails.

To remedy this, we declare weak fairness of the next state. This states that if next is continuously accessible, it must eventually be entered. In effect, we guarantee system progress.

If the system is guaranteed to progress, then it will eventually reach this consensus state!

#### Note:
Be sure to run this model with TwoPhaseLive.cfg or the liveness property will not be checked.
