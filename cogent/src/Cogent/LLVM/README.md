# LLVM Backend of Cogent

## Verified

* Nothing yet

## Finished Implementation

* Core Types
    - Primitive types 
        - Integer types are represented as `iN` using their expected number of bits
        - Bool is represented as an 8-bit integer where 0 = False, otherwise = True)
    - Unit type
        - Represented as an `i8` integer of undefined value, but canonically 0
    - Records, boxed and unboxed
        - LLVM structure types are used, with no packing
    - Variants
        - Represented as a struct with an `i32` tag and a value which takes the shape of the largest parameter to the variant
    - Function types
        - These use pointers to LLVM function types
    - Abstract types, boxed and unboxed, polymorphic and monomorphic
        - These types are globally declared as `type opaque` when they are encountered in an expression
        - The names of a polymorphic abstract type are generated based on their instantiation
        - Boxed types are just pointers to the opaque type
* Core Expressions
    - Unit literal
        - A `i8` is initialised to zero
    - Integer literals
        - A `iN` is initialised to the desired unsigned value
    - Arithmetic, logical, and bitwise binary operators
        - `+` , `-` , `*` , `/` , `%` , `&&` , `||` , `>` , `<` , `<=` , `>=` , `==` , `/=` , `.&.` , `.|.` , `.^.` , `<<` , `>>`
    - Complement and not operators
        - These are implemented identically using `xor` with the `-1` literal
    - Let and letbang bindings
        - A list of in-scope variables is threaded though the compiler
    - Variable expressions
        - The variable is retrieved from the threaded variable list
    - Integer upcasting
        - `zext` is used to zero-extend unsigned integers
    - If-then-else expression
        - Uses `br` and `phi` instructions
    - Record member access expression
        - For unboxed records, `extractvalue` is used
        - For boxed records, we need to `getelementptr` then `load`
    - Record take expression
        - As with member access but variables are also bound
    - Record put expression
        - For unboxed records, `insertvalue` is used
        - For boxed records, we need to `getelementptr` then `store`
    - Record literals
        - Constructed using successive `insertvalue` instructions
    - Variant constructors
        - `insertvalue` inserts the tag and then a casted value
    - Variant case and esac
        - A variant's tag field is used to conditionally branch like if-then-else
    - Variant promotion
        - Purely syntactic, this is a `nop` in the compiled code
    - Function expressions
        - These are converted to global LLVM function references
    - Function application
        - A function is applied using the `call` instruction
* Declarations
    - Function definitions
        - Correspond to LLVM function definitions via `declare`
    - Abstract function declarations
        - Correspond to LLVM abstract declarations via `declare`
    - Abstract type definitions
        - Correspond to LLVM type definitions via `type opaque`
    - Type aliases
        - An earlier stage of compilation substitutes these for us, which is good since `type` doesn't seem to support non-aggregate types

## Hacky Implementation

* `clang` compatible function wrappers which have correctly coerced struct parameters/return types
    - For each function definition, a wrapper is generated which can be called from C
    - For each abstract function declaration, a wrapper is generated which can be called from LLVM
    - Instead of passing structures, these wrappers deal with primitive arguments, or pointers which are casted/loaded appropriately
    - Only designed for `x86-64` , as this is my platform, needs more investigation to work on `x86-32` , `ARMv7` , `ARMv8` which use different size arguments, and also arrays for coercing struct parameters to functions
* `.h` file generation
    - Prototypes are generated for each Cogent function definition as well as abstract functions
    - `typedef` s are emitted for each non primitive type used in the code as well as for argument and return types
    - Implementation is hacky and should be rewritten using quasiquoted C or by reusing existing header generation from C backend
* Function, constructor name sanitisation
    - Very naive and can result in name collisions e.g. `f'` and `f_prime`
* String literals and string types
    - Untested and inconsistent use of pointers vs native arrays, leftover from prototype

## Unsupported

* Language extensions 
    - Built-in arrays
        - They seem straightforward to implement
    - Dargent
        - This seems hard but LLVM does provide ways to do it properly
    - Recursive types
        - I can't estimate the difficulty of this
    - Others?
* Branch likelihood annotation
    - The LLVM syntax exists but it is very confusing
* Compilation without the desugarer
    - Sweet syntax is not supported
