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
* authors claim that intuition behind IMPS more closely corresponds to mathematics than, say, CoC


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
* employs William M. Farmer, one of the main IMPS authors


Current status
--------------

* does not seem to be actively developed
* download link dead
* author (William M. Farmer) did not respond to e-mail


Reference
---------

Farmer, William M., Joshua D. Guttman, and F. Javier Thayer. "IMPS: An interactive mathematical proof system." Journal of Automated Reasoning 11.2 (1993): 213-248.



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
* Ind~1~, Ind~2~, ..., Ind~m~

### Function types

* Given types $\alpha_1, \dots, \alpha_n, \alpha_{n+1}$.
* Then $\alpha_1, \dots, \alpha_n \rightarrow \alpha_{n+1}$ is a function type.

### Properties

* multi-sorted: $m$ may be >1
* multi-variate: $n$ may be >1


Kinds
-----

* $\alpha$ is of *kind* Ind if

    - $\alpha$ = Ind~i~ for some i or
    - $\alpha = \alpha_1, \dots, \alpha_n \rightarrow \alpha_{n+1}$ and
  $\alpha_{n+1}$ is of kind Ind

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


Subtypes
--------

* Subtypes are subsets of denotations of their types
* Examples:
    - $\mathbb{N} \subset \mathbb{Z} \subset \mathbb{Q} \subset \mathbb{R} \subset$ Ind~1~
    - $\mathbb{N} \rightarrow \mathbb{R} \subset$ Ind~1~ $\rightarrow$ Ind~1~
* $\lambda x : \mathbb{N}. (f : \mathbb{R} \rightarrow \mathbb{R}) x$ well-typed


Theorem Proving
===============


Deduction graphs
----------------

### Nodes

* inference node
* sequent node: $\Gamma \Rightarrow A$ with $\Gamma$ context, $A$ proposition

### Groundedness

* inference: grounded if all child sequents grounded
* sequent: grounded if some child inference grounded


Why deduction graphs?
---------------------

* sequents can have multiple "realising" inferences
* loops indicate mutually provable theorems
* proof analysis


Building a graph
----------------

### Allowed graph operations

* adding sequent nodes
* primitive inferences:
    - add new child sequents
    - connect to parent sequent

### Primitive inferences

* ~ 30 primitive inferences, such as $\beta$-reduction, equality substitution, cut, elimination of Iota-expressions etc.
* special inferences: macete, simplification

### Strategies

combine primitive inferences, like tactics in HOL


Simplification
--------------

### Problem

* input: context $\Gamma$, expression $e$, theory $\mathcal{T}$
* output $e'$ s.t. $\Gamma, \mathcal{T} \models e = e'$

### Definedness

* example: $\Gamma \models 1/x - 1/x = 0$ only valid if $\Gamma \models 1/x \downarrow$
* simplifier creates "convergence requirements"



Theory-supported reasoning
==========================


Definedness reasoning
---------------------

Automation relies on following information:

* range: $\forall x : \alpha. \phi(x, f(x))$
* domain: $\forall x : \alpha. \psi(x) \supset (g(x) \downarrow)$
* sort-definedness: $\forall x : \alpha. \psi(x) \supset (g(x) \downarrow \beta)$ (definedness of $g(x)$ w.r.t. a sort $\beta$)


Macetes
-------

* Portuguese for "clever trick"
* apply theorems to sequents in deduction graph

### Macete types

* theorem macete: automatically generated for each theorem
* compound macete: combine theorey macetes with other macetes such as $\beta$-reduction or simplification
* transportable macete: apply theorem outside of its theory



Technical stuff
===============


Implementation
--------------

### Versions

* Version 1.2: written in the T programming language (Scheme dialect)
* Version 2.0: adapted to Common Lisp (by emulation of T)

### Interface

GNU Emacs


IMPS Theory Library
-------------------

* 99 theories
* mathematics: from "Abelian groups" to "vector spaces"
* networks: e.g. routed-networks, octets, protocol-theory
* automata: hoare-machines, state-machines
* software verification: verified Scheme dialect


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


Conclusion
----------

### Specialities

* partiality
* subtypes
* deduction graphs
* LISP-based

### Disadvantages

* dead


The end
-------

Merci beaucoup pour votre attention !
