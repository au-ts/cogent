/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

static unit_t unit = { .dummy = 1 };

static inline unit_t cogent_debug(char* str) {
	printf ("%s", str);
    return unit;
}

static inline unit_t cogent_debug_u32 (u32 arg) {
	printf ("%u", (unsigned)arg);
    return unit;
}

static inline unit_t cogent_debug_u64 (u64 arg) {
	printf ("%llu", (unsigned long long)arg);
	return unit;
}

static inline unit_t cogent_debug_u64_hex (u64 arg) {
	printf ("%llx", (unsigned long long)arg);
	return unit;
}

