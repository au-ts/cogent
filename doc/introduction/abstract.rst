************************************************************************
                Abstract Types and Polymorphic Functions
************************************************************************

In the previous example, we have shown some of the ``libgum`` functions---they are
*abstract functions*, in the sense that we only declare them in |cogent|, and defer
their definitions to C. |cogent| also offers *abstract types*. An abstract type is a 
type that only gets declared in |cogent|, but is defined in C.

If we want to declare two abstract types ``A`` and ``B``, we write in |cogent|:

.. code-block:: haskell

  type A
  type B

|cogent| assumes nothing but that they are boxed types, allocated on the heap and is access by a pointer.
Boxed abstract types are by definition linear in |cogent|'s type system. Whenever you use a value of type
``A`` in |cogent|, it will always be a pointer to type ``A`` in the generated C code.

In C, we can give concrete definitions for these types, for example:

.. code-block:: c

  typedef char A;
  typedef struct { int b; } B;

.. note:: If in your |cogent| source file, there're only type definitions and no function definitions, then
          |cogent| will not generate any types in the C file. And |cogent| will only generate types that
          get used by at least one function.

Now we need to add some |cogent| functions to work on these types.
For example, we define a very simple |cogent| function::

  swapDrop : all (a, b, c :< DS). (a, b, c) -> (b, a)
  swapDrop (a, b, c) = (b, a)

``swapDrop``, as its name suggests, it swaps the first two components in the argument tuple,
and drops the last element. ``all (a, b, c :< DS)`` universally quantifies type variables
``a``, ``b`` and ``c``. Additionally, it says that ``c`` is constrained to have ``DS`` permissions
(see more details in :ref:`permissions`). ``D`` and ``S`` mean that the type ``c`` has to be
``D``\ iscardable and ``S``\ hareable respectively, i.e. non-linear, and that's why the third component in the tuple
can be dropped (or, discarded). Strictly speaking, ``S`` is not needed here, as we don't share it.
But it's more conventional to use ``DS`` together, as ``D`` and ``S`` together denote linearity.

The ``main.ac`` file has some trickiness:

.. code-block:: c
  :linenos:
  :emphasize-lines: 4,5,7,17

  $esc:(#include <stdlib.h>)
  $esc:(#include <stdio.h>)
  
  typedef char A;
  typedef struct { int b; } B;
  
  #include "swap-drop.c"
  
  int main() {
    A *a = (A*)malloc(2 * sizeof(char));
    B *b = (B*)malloc(sizeof(B));
    a[0] = '!';
    a[1] = '\0';
    b->b = 42;
  
    $ty:((A,B,U32)) arg = { .p1 = a, .p2 = b, .p3 = 12 };
    $ty:((B,A)) ret = $exp:(swapDrop[A,B,U32])(arg);
    
    printf("fst = %u\n", ret.p1->b);
    printf("snd = %s\n", ret.p2);
    return 0;
  }

On line 4 and 5, we give definitions for types ``A`` and ``B``, as we have discussed above.
It's worthy noting that on line 7, we include the generated C file. It has to come after
the definitions of ``A`` and ``B``, as the generated C code rely on the definition of them.
Finally on line 17, we use an antiquote ``$exp`` to refer to the |cogent| function ``swapDrop``.
The type arguments of this function have to be fully applied, as in this ``main.ac`` file,
the |cogent| compiler doesn't know what instantiation it has, thus unable to infer.

As before, we need an ``entrypoints.cfg`` file to pass to the ``--entry-funcs`` argument. In this
file, the only function needs to be included is ``swapDrop[A,B,U32]``. Again, for the same reason,
the type arguments have to be fully applied. As the programmer, you are responsible for ensuring
that the ones passed to ``--entry-funcs`` are consistent with what get used in the antiquoted C files.
The |cogent| compiler doesn't perform any sanity checks.


Example: polymorphic abstract types
===================================

Now let's explore some more advanced features of |cogent|. |cogent| allows types to be parametric, including
abstract types. Typical examples include containers: arrays, lists, trees, etc.
Functions operating on these parametric abstract types are polymorphic, and share the same interface.
These functions are normally parametrically polymorphic, meaning that they are generic over types.

.. note:: |cogent| allows for ad hoc definitions of some instances of a polymorphic function,
          but we won't go into it in this example. We only consider parametric polymorphism here.

.. code-block:: haskell

  include <gum/common/wordarray.cogent>
  
  map : WordArray U32 -> WordArray U32
  map arr = let view = wordarray_view (arr, 3, 6, 1)
            and view' = wordarray_map_view (view, triple)
             in wordarray_unview view'
  
  triple : U32 -> U32
  triple x = 3 * x

In this example, we write a small |cogent| function ``map`` which maps a slice
of a wordarray. A wordarray is a dynamically allocated array in C, with
unsigned integers (of the same type) as its elements. ``WordArray a`` is an abstract
type defined in `cogent/lib/gum/common/wordarray.cogent <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/common/wordarray.cogent>`__, where ``a`` is the element type of that array.
``wordarray_view (arr, fr, to, st)`` is a polymorphic function over the element type ``a``, creating a
writable *view* into a slice of an array ``arr``, starting from the ``fr``-th element (inclusive), with step
``st``, and ending at the ``to``-th element (exclusive).
``wordarray_map_view`` maps over every element in the view, and returns the updated slice. The updates
are performed in-place, resulting in more performant C code. Finally ``wordarray_unview`` converts a view
back to a regular array. This piece of |cogent| program is relatively simple. 

In the companion ``main.ac`` file, the ``main`` function is straightforward: we call the |cogent| ``map``
function as ``map (arr)``. Here we don't even need to use the ``$exp`` antiquote, as we can already
know that the generated C function name of ``map`` is identical to its |cogent| name, given that
this function is monomorphic. 

The antiquoted C file giving the definitions of the abstract functions for wordarray can be found
in `cogent/lib/gum/anti/wordarray.ac <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/anti/wordarray.ac>`__
and is standard. What's not so obvious is how to define the abstract type of wordarray.

Unlike the previous example that we could define the (monomorphic) abstract types in the ``main.ac`` file,
here we need to create another type of antiquoted file---a ``.ah`` file---antiquoted header file.
The antiquoted header files are passed to the ``--infer-c-types`` argument, contrary to the ``--infer-c-funcs`` argument.
The reason why ``.ah`` files are different from ``.ac`` files is that, we know what
types a polymorphic function should be instantiated to according to the explicit type applications in the ``.ac`` file,
as in ``$exp:(swapDrop[A,B,U32])`` in the previous example. For types, however, we
work out the instantiations depending on what instances are **used** in your |cogent| functions.

.. note:: It's only used if it's a dependency of at least one function specified in ``--entry-funcs``.

The definition of ``WordArray a`` is given below (also in the repository in
`cogent/lib/gum/anti/abstract/WordArray.ah <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/anti/abstract/WordArray.ah>`__):

.. code-block:: c

  struct $id:(WordArray a) {
  	int len;
  	$ty:a* values;
  };
  
  typedef struct $id:(WordArray a) $id:(WordArray a);

In the |cogent| standard library, a wordarray is defined to be a struct, consisting of two fields:
``len`` stores the length of the wordarray, and ``values`` is a C array holding the contents.

Let's come back to the ``main.ac`` file. The first few lines look like:

.. code-block:: c

  $esc:(#include <stdio.h>)
  $esc:(#include <stdlib.h>)
  $esc:(#include <string.h>)
  
  #include "mapper.c"
  #include <wordarray.ac>

We only need to include the ``.ac`` files, as the ``.ah`` files will be automatically
included in the generated ``mapper.h`` file. After all, the function declarations and definitions
there rely on the definitions of the abstract types.

We can have a brief look at how they are included:

.. code-block:: c

  #include <abstract/WordArray_u32.h>
  #include <abstract/View_WordArray_u32.h>
  struct t2 {
      View_WordArray_u32 p1;
      t1 p2;
  } ;

Once the parametric abstract type is needed, the |cogent| compiler will generate lines
to include the monomorphised definitions of the parametric types. 

The build command (in a Makefile) is:

.. code-block:: make

	cogent $(SRC) -g -o$(OUTPUT) \
		--abs-type-dir="$(ABSDIR)" \
		--infer-c-types="$(AHFILES)" \
		--infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--entry-funcs=entrypoints.cfg

``$(ABSDIR)`` is the directory containing the generated definitions of parametric types.
All the generated header files will be placed in ``$(ABSDIR)/abstract``, which
must already exist before this command is run. ``$(AHFILES)`` needs to include all the
needed ``.ah`` files, and ``$(ACFILES)`` here is only the ``main.ac``, since the other ``.ac`` files
are already included in ``main.ac``.

The code for this example can be found in the `repository <https://github.com/NICTA/cogent/tree/master/cogent/examples/mapper>`__.

