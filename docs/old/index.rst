========================================================================
                                 Cogent
========================================================================

:Version:	3.0.0
:License:	GPL-2.0-only
:Homepage:	<https://ts.data61.csiro.au/projects/TS/cogent.pml>
:Repository:	<https://github.com/NICTA/cogent>

Welcome to Cogent's documentation!
==================================

Cogent is a restricted, polymorphic,
higher-order and purely functional language
with uniqueness types
and without the need for a trusted runtime
or garbage collector.

**Cogent is restricted.**
Cogent is *not* a general-purpose language.
It omits certain features
that one might come to expect
from a programming language.
For instance, Cogent doesn't support general recursion.

**Cogent is polymorphic.**
Parametrically.
This is similar to templates in C++,
or generics in Rust.

**Cogent is higher-order.**
Functions are values---they can be function arguments.

**Cogent is purely functional,**
in the sense of
the functional programming paradigm:
functions are stateless,
and the result of a function is deterministically defined
by the arguments to the function,
just like a mathematical function.

**Cogent has uniqueness types**:
as a means to control references,
every linear object
(roughly equivalent to heap-allocated object)
can only have one unique reference.

**Cogent has no trusted runtime.**
Cogent compiler generates C code,
so the trusted component is limited to
the C runtime system.

**Cogent has no garbage collector.**
Since Cogent compiler generates C code,
we would manage memory manually,
like we do in any C program.

**Cogent has a certifying compiler.**
Cogent is designed for writing and formally
verifying systems code. That's why we compromise
on language expressiveness for verifiability.


This documentation is for anyone who wants to try out or use Cogent.
We assume that you have a basic understanding of the Cogent project already,
including what Cogent is about,
the approach that we take in this research,
and what Cogent brings you.
If you don't, you may want to first read about
the `Cogent project`_.

.. _Cogent project: http://ts.data61.csiro.au/projects/TS/cogent.pml

.. toctree::
   :caption: Table of contents
   :maxdepth: 2
   :numbered:

   preamble
   quickstart
   install
   surface
   antiquote
   compiler
   verification
   meta

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
