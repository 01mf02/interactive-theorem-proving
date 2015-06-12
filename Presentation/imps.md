% IMPS
% Michael Färber
% June 15, 2015

Introduction
============


Overview
--------

* IMPS = Interactive Mathematical Proof System
* simple type theory with partial functions and subtypes
* inference based on *deduction graphs* (similar to derivations in sequent calc.)
* intuition behind IMPS more closely corresponds to mathematics than, say, CoC
* macete


The MITRE Corporation
---------------------

* developed IMPS from 1990 to 2006
* non-profit organisation
* operates spin-off research institutes of MIT
* military bias -- works for:
    - Department of Defense
    - Department of Homeland Security
    - US Air Force
* based in Massachusetts and Virginia


McMaster University
-------------------

* in Ontaria, Canada
* 838 km from MIT
* currently hosts IMPS website
* employs William M. Farmer, author of IMPS


Current status
--------------

* does not seem to be actively developed
* download link dead


Logic
=====


LUTINS
------

* Logic of Undefined Terms for Inference in a Natural Style
* French for "imp" ("Wichtel")
* realises higher-order predicate logic
* derived from PF, i.e. a version of Church's simple type theory with partiality


Types
-----

### Base types

* Prop
* Ind~1, Ind~2, ..., Ind~m

### Function types

* Given types $\alpha_1, \dots, \alpha_n, \alpha_{n+1}$.
* Then $\alpha_1, \dots, \alpha_n \rightarrow \alpha_{n+1}$ is a function type.

### Properties

* multi-sorted: $m$ may be >1
* multi-variate: $n$ may be >1


Kinds
-----

* $\alpha$ is of *kind* Ind if

    - $\alpha$ = Ind~i for some i or
    - $\alpha = \alpha_1, \dots, \alpha_n \rightarrow \alpha_{n+1}$ and
  $\alpha_{n+1} is of kind Ind

* Otherwise, $\alpha$ is of kind Prop.

### Definedness

* All values of kind Prop are defined.
* There exist values of kind Ind that are undefined.


Constructors
------------

* Lambda: $\lambda$
* Equality: =
* Function application
* Iota: I

### Iota

* definite description operator
* $I x. P x$ denotes unique $x$ satisfying $P$
* Example: $\lambda x y. I z. x * z = y$.


Implementation
==============

Versions
--------

* Version 1.2: written in the T programming language (Scheme dialect)
* Version 2.0: adapted to Common Lisp (by emulation of T)


Interface (Emacs)



IMPS Theory Library
===================

Stuff
-----

* 99 theories
* mathematics: from "Abelian groups" to "vector spaces"
* networks: e.g. routed-networks, octets, protocol-theory
* automata: hoare-machines, state-machines



Example
=======

Example
-------

~~~ commonlisp
(def-theorem factorial-definedness 
    "forall(m:zz,#(m!))"
    (proof
      (
        (unfold-single-defined-constant (0) factorial)
        insistent-direct-inference
        beta-reduce-repeatedly
        (apply-macete-with-minor-premises prod-definedness)
        simplify
        )
      )
    (theory h-o-real-arithmetic)
    (usages d-r-convergence))
~~~


Partiality
----------

* `#(t)` expresses that a term `t` is defined
* `?s` expresses that `s` is undefined
