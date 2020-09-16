************************************************************************
                                |cogent|
************************************************************************

:Version:	2.9
:License:	GPL-2.0-only
:Homepage:	<https://ts.data61.csiro.au/projects/TS/cogent.pml>
:Repository:	<https://github.com/NICTA/cogent>


Welcome!
|cogent| is a restricted, polymorphic,
higher-order and purely functional language
with uniqueness types
and without the need for a trusted runtime
or garbage collector.

|cogent| is **restricted**.
|cogent| is *not* a general-purpose language:
it omits certain features
that one might come to expect
from a programming language.
For instance, |cogent| doesn't support general recursion.

|cogent| is **polymorphic**,
parametrically.
This is similar to templates in C++,
or generics in Rust.

|cogent| is **higher-order**.
Functions are values --- they can be function arguments.

|cogent| is **purely functional**,
in the sense of
the functional programming paradigm:
functions are stateless,
and the result of a function is deterministically defined
by the arguments to the function,
just like a mathematical function.

|cogent| has **uniqueness types**:
as a means to control references,
every linear object
(roughly equivalent to heap-allocated object)
can only have one unique reference.

|cogent| has **no trusted runtime**.
The |cogent| compiler generates C code,
so the trusted component is limited to
the C runtime system.

|cogent| has **no garbage collector**:
since the |cogent| compiler generates C,
we manage memory manually,
as we would in any C program.

|cogent| has a **certifying compiler**.
|cogent| is designed for writing and formally
verifying systems code. That's why we compromise
on language expressiveness for verifiability.


This documentation is for anyone who wants to try out or use |cogent|.
We assume that you have a basic understanding of the |cogent| project already,
including what |cogent| is about,
the approach that we take in this research,
and what |cogent| brings you.
If you don't, you may want to first read about
the `Cogent project`_.

.. _Cogent project: http://ts.data61.csiro.au/projects/TS/cogent.pml

.. toctree::
   :maxdepth: 2

   introduction
   reference
   appendices


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
