# Todo

## Important
* Change the Eq instance of DataLayout to ignore SourcePos information
  * Maybe should use the trees that grow approach to add this information?
* Add support for attaching layouts to types to the surface syntax, and then add lots of tests to the compiler to test custom layouts

## Other
* Fix antiquoted-C test pass_static_array -
  * Need to make a way of specifying which additional getters/setters should be generated for the antiquoted C. Currently, there is no need for the getter in the Cogent code, so it isn't generated. But it is needed in the C code to replace the code `args.p2->f` with `d?_get_f(args.p2)`.
* Think about whether we need to add syntax into the language to allow explicit specification of the size of a layout
* Refactor the code generation code into several largely independent files with explicit imports (to improve readability of code)
  * Particularly the code which does type generation
  * The StrlType thing doesn't really make sense - I feel like custom equality on normal Cogent types which ignores whether fields are/aren't taken would suffice (there should be an equivalence relation on cogent types such that each equivalence class gets mapped to a unique C type)
* Check what kind of machine code is being generated
  * Make sure to try non-default layouts and all kinds of types embedded in the boxed record
* Add a compiler flag to set the variable which decides the compilation architecture
  * In future this could be decided automatically based on the architecture that gcc is compiling for
    * Partha said could use `gcc -dumpmachine` that shows the architecture that the compiler is built for
    * use `#if` in Cogent code and   `$escstm:()` in the antiquoted C code.
  * Also figure out how to switch on the architecture in a `#IF ... #ELSE ... #ENDIF` C preprocessor statement, so we can have different layouts for different architectures
  * Potentially add Cogent surface syntax for switching on architecture/architecture dependent offsets - to be desugared to the existing core layout structures.
* More testing
  * Create more antiquoted-C tests
    * Some which actually print out all the bits of the data structure after setting to check that the correct bits are being set (the existing tests only check that setting and then getting gets what was set)
    * Some which check that the *default layouts* actually match up with the old layouts for boxed records
    * Try a large scale test (like BilbyFS, except that won't work as BilbyFS has unboxed abstract types in boxed records)
* Implement embedded  `TProduct _ _` (the type of `Tuple e1 e2` expressions, ie. pairs)
* Core type checker for data layouts after monomorphisation is only partially implemented, must be finished and integrated with rest of compiler
* Figure out how to handle endianness
  * Should be possible to expand the dargent syntax to allow decomposing the layout of primitive types into an array of bitranges, each of which doesn't have to be contiguous in memory (like in the core syntax after splitting into aligned bit ranges in the CodeGen stage).
  * Opposite endianess would be a layout like `[1B at 3B, 1B at 2B, 1B at 1B, 1B]` for `U32`.
* Add fixed size arrays to types allowed to be included in boxed records (using while loops in the code generation) - this may be non-trivial


# Proposed new surface Syntax
`{ fi : Ti }` - boxed record with default layout
`#{ fi : Ti }` - unboxed record
`{ fi : Ti } with layout { fi : Li }` - boxed record with custom layout

* Backwards compatible
* Need to add the `$` type operator to the parser
* Layout syntax has already been added to the parser, but I have some proposals for changes before it is made public:

* `record { fi : Li }` should become `{fi : Li}`
* `variant (Ltag) { Ai(vi) Li }` should become
```
Ltag
| v1 -> A1 L1
| v2 -> A2 L2
```

eg.

```
< Success U32 | Fail () > $
(1b at 4B
  | 0 -> Success (4B at 0B)
  | 1 -> Fail 0B)
```

# 2. Layout polymorphism
`f: forall l. { a : U8 } $ l -> Bool`
* Add syntax for layout variables
* Add syntax for insantiating layout variables - layout application.
* `f { a : 8b at 8b } 0`

Need predicate that a layout and type match!

# 3. Layout inference
`{ fi : Ti }` now is a shorthand for `forall l. { fi : Ti } $ l` everywhere except in C FFI declarations, in which case it is a shorthand for the boxed type with the default layout.

This is good because existing functions, such as
`f : { a : U8 } -> Bool` will still work in the existing code as is, because the implicit layout variable will be inferred to be the default layout by layout inference. But, we additionally gain the ability to call the function `f` on boxed values `{ a: U8}` with non-default layouts.

The only way we get boxed records into cogent is through the C FFI, and so we should restrict the layout polymorphism allowed on the C FFI??? Because the layout has to be monomorphised eventually.

# Nested pattern matching:
* How does put/take work - eg. record in record. take a field of the record in the record. Can I take the record itself?
* Extend syntax
* improves performance

