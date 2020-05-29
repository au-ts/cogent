-- Hey, Emacs!  This isn't actually C; it's really -*- cogent -*-.

#ifdef VERIFICATION

--
-- Logging is disabled under verification, as the AutoCorres C parser
-- chokes on string literals.  Instead, we exploit the C preprocessor to
-- make debug invocations disappear when verifying.
--

-- cogent_log2: U32 -> U32
#define cogent_log2(x) (x)

-- cogent_assert: Bool -> ()
#define cogent_assert(x) ()

-- cogent_warn: String -> ()
#define cogent_warn(x) ()

-- cogent_warn_u16: U16 -> ()
#define cogent_warn_u16(x) ()

-- cogent_warn_u32: U32 -> ()
#define cogent_warn_u32(x) ()

-- cogent_warn_u64: U64 -> ()
#define cogent_warn_u64(x) ()


-- cogent_debug: String -> ()
#define cogent_debug(x) ()

-- cogent_debug_bool: Bool -> ()
#define cogent_debug_bool(x) ()

-- cogent_debug_u8: U8 -> ()
#define cogent_debug_u8(x) ()

-- cogent_debug_u16: U16 -> ()
#define cogent_debug_u16(x) ()

-- cogent_debug_u32: U32 -> ()
#define cogent_debug_u32(x) ()

-- cogent_debug_u32_oct: U32 -> ()
#define cogent_debug_u32_oct(x) ()

-- cogent_debug_u32_hex: U32 -> ()
#define cogent_debug_u32_hex(x) ()

-- cogent_debug_u64: U64 -> ()
#define cogent_debug_u64(x) ()

-- cogent_debug_u64_hex: U64 -> ()
#define cogent_debug_u64_hex(x) ()


-- cogent_log: (U32, String) -> ()
#define cogent_log(l,x) ()

-- cogent_log_bool: (U32, Bool) -> ()
#define cogent_log_bool(l,x) ()

-- cogent_log_u8: (U32, U8) -> ()
#define cogent_log_u8(l,x) ()

-- cogent_log_u16: (U32, U16) -> ()
#define cogent_log_u16(l,x) ()

-- cogent_log_u32: (U32, U32) -> ()
#define cogent_log_u32(l,x) ()

-- cogent_log_u32_oct: (U32, U32) -> ()
#define cogent_log_u32_oct(l,x) ()

-- cogent_log_u32_hex: (U32, U32) -> ()
#define cogent_log_u32_hex(l,x) ()

-- cogent_log_u64: (U32, U64) -> ()
#define cogent_log_u64(l,x) ()

-- cogent_log_u64_hex: (U32, U64) -> ()
#define cogent_log_u64_hex(l,x) ()

#endif -- defined(VERIFICATION)
