(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter \<open>Example: seL4\<close>

theory TestSEL4
  imports CParser.CTranslation
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../src_ext/l4v/src/tools/autocorres/test-seL4/TestSEL4.thy\<close>\<close>

declare [[allow_underscore_idents]]
declare [[ML_print_depth = 500]] \<comment> \<open>Any number large enough for @{command install_C_file}
                                     to completely serialize all provided values\<close>

(*
 * Test to check if Isabelle/C can parse the entire seL4 sources.
 * Test to check if all C parsed values are equal to the original parser modulo positions.
 *)

install_C_file all_parsing no_cpp parse_then_stop
               \<comment> \<open>The following file can be meanwhile CTRL-clicked on it:\<close>
               \<open>../../../src_ext/l4v/generated/spec/cspec/c/build/ARM/kernel_all.c_pp\<close>
(*19 s on MacOS i7 processor. 27,9 kloc, 790 kb. Just parsing, no semantic backend ectivated.*)


text\<open>This is just a local test for some lines of the kernel. Some Semantics included. \<close>

install_C no_cpp kernel_not_all \<open>
# 1 "kernel_all_copy.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "kernel_all_copy.c"
# 1 "/seL4/src/api/faults.c"
/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 */

typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;

typedef signed char int8_t;
typedef signed short int16_t;
typedef signed int int32_t;
typedef signed long long int64_t;

/** MODIFIES: */
void __builtin_unreachable(void);

/** MODIFIES:
    FNSPEC
        halt_spec: "\<Gamma> \<turnstile> {} Call halt_'proc {}"
*/
void halt(void) __attribute__((__noreturn__));
void memzero(void *s, unsigned long n);
void *memset(void *s, unsigned long c, unsigned long n) __attribute__((externally_visible));
void *memcpy(void* ptr_dst, const void* ptr_src, unsigned long n) __attribute__((externally_visible));
int __attribute__((__pure__)) strncmp(const char *s1, const char *s2, int n);
long __attribute__((__const__)) char_to_long(char c);
long __attribute__((__pure__)) str_to_long(const char* str);

int __builtin_clzl (unsigned long x);
int __builtin_ctzl (unsigned long x);

/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC clzl_spec:
  "\<forall>s. \<Gamma> \<turnstile>
    {\<sigma>. s = \<sigma> \<and> x_' s \<noteq> 0 }
      \<acute>ret__long :== PROC clzl(\<acute>x)
    \<lbrace> \<acute>ret__long = of_nat (word_clz (x_' s)) \<rbrace>"
*/
static inline long
__attribute__((__const__)) clzl(unsigned long x)
{
    return __builtin_clzl(x);
}

/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC ctzl_spec:
  "\<forall>s. \<Gamma> \<turnstile>
    {\<sigma>. s = \<sigma> \<and> x_' s \<noteq> 0 }
      \<acute>ret__long :== PROC ctzl(\<acute>x)
    \<lbrace> \<acute>ret__long = of_nat (word_ctz (x_' s)) \<rbrace>"
*/
static inline long
__attribute__((__const__)) ctzl(unsigned long x)
{
    return __builtin_ctzl(x);
}

int __builtin_popcountl (unsigned long x);

/** DONT_TRANSLATE */
static inline long
__attribute__((__const__)) popcountl(unsigned long mask)
{

    unsigned int count; // c accumulates the total bits set in v
    for (count = 0; mask; count++) {
        mask &= mask - 1; // clear the least significant bit set
    }

    return count;
}

typedef int __assert_failed_long_is_32bits[(sizeof(unsigned long) == 4) ? 1 : -1];

typedef unsigned long word_t;
typedef signed long sword_t;
typedef word_t vptr_t;
typedef word_t paddr_t;
typedef word_t pptr_t;
typedef word_t cptr_t;
typedef word_t node_id_t;
typedef word_t cpu_id_t;
typedef word_t dom_t;

typedef uint8_t hw_asid_t;

enum hwASIDConstants {
    hwASIDMax = 255,
    hwASIDBits = 8
};

/* for libsel4 headers that the kernel shares */
typedef word_t seL4_Word;
typedef cptr_t seL4_CPtr;
typedef uint32_t seL4_Uint32;
typedef uint16_t seL4_Uint16;
typedef uint8_t seL4_Uint8;
typedef node_id_t seL4_NodeId;
typedef dom_t seL4_Domain;
typedef paddr_t seL4_PAddr;

typedef struct kernel_frame {
    paddr_t paddr;
    pptr_t pptr;
    int armExecuteNever;
} kernel_frame_t;
# 16 "/seL4/include/basic_types.h" 2

enum _bool {
    false = 0,
    true = 1
};
typedef word_t bool_t;

typedef struct region {
    pptr_t start;
    pptr_t end;
} region_t;

typedef struct p_region {
    paddr_t start;
    paddr_t end;
} p_region_t;

typedef struct v_region {
    vptr_t start;
    vptr_t end;
} v_region_t;

/* equivalent to a word_t except that we tell the compiler that we may alias with
 * any other type (similar to a char pointer) */
typedef word_t __attribute__((__may_alias__)) word_t_may_alias;

struct seL4_MessageInfo {
    uint32_t words[1];
};
typedef struct seL4_MessageInfo seL4_MessageInfo_t;

static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_new(uint32_t label, uint32_t capsUnwrapped, uint32_t extraCaps, uint32_t length) {
    seL4_MessageInfo_t seL4_MessageInfo;

    /* fail if user has passed bits that we will override */
    ;
    ;
    ;
    ;

    seL4_MessageInfo.words[0] = 0
        | (label & 0xfffffu) << 12
        | (capsUnwrapped & 0x7u) << 9
        | (extraCaps & 0x3u) << 7
        | (length & 0x7fu) << 0;

    return seL4_MessageInfo;
}

static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_label(seL4_MessageInfo_t seL4_MessageInfo) {
    uint32_t ret;
    ret = (seL4_MessageInfo.words[0] & 0xfffff000u) >> 12;
    /* Possibly sign extend */
    if (0 && (ret & (1u << (31)))) {
        ret |= 0x0;
    }
    return ret;
}

static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_capsUnwrapped(seL4_MessageInfo_t seL4_MessageInfo) {
    uint32_t ret;
    ret = (seL4_MessageInfo.words[0] & 0xe00u) >> 9;
    /* Possibly sign extend */
    if (0 && (ret & (1u << (31)))) {
        ret |= 0x0;
    }
    return ret;
}

static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_set_capsUnwrapped(seL4_MessageInfo_t seL4_MessageInfo, uint32_t v32) {
    /* fail if user has passed bits that we will override */
    ;
    seL4_MessageInfo.words[0] &= ~0xe00u;
    seL4_MessageInfo.words[0] |= (v32 << 9) & 0xe00u;
    return seL4_MessageInfo;
}

static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_extraCaps(seL4_MessageInfo_t seL4_MessageInfo) {
    uint32_t ret;
    ret = (seL4_MessageInfo.words[0] & 0x180u) >> 7;
    /* Possibly sign extend */
    if (0 && (ret & (1u << (31)))) {
        ret |= 0x0;
    }
    return ret;
}
\<close>

context \<comment> \<open>The following binding can be meanwhile CTRL-clicked on it:\<close>
        kernel_not_all
        begin end

end
