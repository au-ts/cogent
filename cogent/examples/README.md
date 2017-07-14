# Examples in Cogent

A collection of example Cogent programs demonstrating common features in Cogent and how it integrates with non-Cogent code (such as C).

It contains the following examples:
* **hello-world**:
  A very basic "Hello World" example with dedicated comments for new users.
* **adder**:
	Adds two given unsigned 32 bit integers.
* **list**:
	Basic list implementation for unsigned 32 bit integers. Most of the functionality is implemented in antiquoted C as opposed to Cogent to maintain a conventional functional programming style.
* **fizzbuzz**:
	Lists the first 100 integers, except every multiple of 3 is replaced with "Fizz", every multiple of 5 is replaced with "Buzz" and every multiple of both is replaced with "FizzBuzz".
* **search**:
    Search on a buffer for a record type element which contains a certain string in a certain field. This example models our pathological case for bad performance -- we cannot directly access
    contents on the buffer, but have to deserialise them for the sake of linearity.
