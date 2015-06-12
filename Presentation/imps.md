% IMPS
% Michael Färber
% June 15, 2015

Introduction
============


Overview
--------

* IMPS = Interactive Mathematical Proof System
* simple type theory with partial functions
* inference based on *deduction graphs* (similar to derivations in sequent calc.)
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


Types and kinds
---------------

### Types

* Prop
* Ind~1, Ind~2, ..., Ind~n

### Kinds

* Prop
* Ind (type $\alpha$ is of kind Ind iff $\alpha$ = ...)





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