This is a simple iterator built in Cogent.

The iterator simply breaks the common components of a C while loop into
functions and a value which are defined in Cogent source. This makes the
job of executing the iterator in C relatively simple. Proving
termination for this iterator may be more difficult.

The `Iter.cogent` contains the definition of the iterator (and a few
supporting functions for printing) and an implementation of the
Fibonacci sequence and FizzBuzz using the iterator.

`main.ac` provides a main function that invokes the cogent program,
implementation of the iterate function which executed an iterator to
completion and implementation of printing functions.

The makefile is designed to demonstrate the bare minimum needed to make
a fully functional program compile using the existing cogent tooling.
