# Twovar

Assorted variants of twophase commit, modeled in TLA+. These are manually defined examples designed to illustrate different environmental variations that may impact robustness.

## Motivation

This repository is tests the notion of software robustness. While formally defined in *A behavioral notion of robustness for software systems, by Zhang et al*, (https://eskang.github.io/assets/papers/fse20-robustness.pdf), robustness can be described (imprecisely) as the number of *environmental* variations a system can tolerate while still satisfying its properties.

A system's *environment* is all of the external factors that influence it -- for instance, human users, or unreliable networks. A good system should be able to tolerate some deviations from expected behavior -- for instance, a user accidentally pressing the wrong button -- while still working.

So we evaluate robustness by seeing what

### Twophase Commit
In our case, we consider the twophase commit protocol for atomic commitment. 

Twophase commit can be decomposed into three logical entities:
1. The transaction manager
2. The resource managers
3. The environment both entities interact with while passing messages. This can be though of as the network.

### The Robustness Question

So the network is our environment. What sort of variations might a network have?

What if it's an unreliable network that drops packets?

What if a malicious actor sends erroneous messages to the various entities?

These are the sort of environmental variations we seek to answer!

