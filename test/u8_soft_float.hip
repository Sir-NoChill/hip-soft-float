// uint8_t-based multi-precision arithmetic implementation
// All operations must use only uint8_t arithmetic

typedef struct {
    uint8_t bytes[4]; // Little endian: bytes[0] = LSB, bytes[3] = MSB
} u32_t;

typedef float fp_t;

// Constants for single precision IEEE-754
#define SIGNIFICAND_BITS 23
#define EXPONENT_BITS 8
#define TYPE_WIDTH 32
#define MAX_EXPONENT ((1 << EXPONENT_BITS) - 1)
#define EXPONENT_BIAS (MAX_EXPONENT >> 1)

// Helper functions for u32_t operations

// Set u32_t to zero
__device__ static inline void u32_zero(u32_t *a) {
    a->bytes[0] = a->bytes[1] = a->bytes[2] = a->bytes[3] = 0;
}

// Set u32_t from uint32_t
__device__ static inline void u32_from_u32(u32_t *dest, uint32_t src) {
    dest->bytes[0] = (uint8_t)(src & 0xFF);
    dest->bytes[1] = (uint8_t)((src >> 8) & 0xFF);
    dest->bytes[2] = (uint8_t)((src >> 16) & 0xFF);
    dest->bytes[3] = (uint8_t)((src >> 24) & 0xFF);
}

// Convert u32_t to uint32_t
__device__ static inline uint32_t u32_to_u32(const u32_t *a) {
    return ((uint32_t)a->bytes[3] << 24) |
           ((uint32_t)a->bytes[2] << 16) |
           ((uint32_t)a->bytes[1] << 8) |
           (uint32_t)a->bytes[0];
}

// Copy u32_t
__device__ static inline void u32_copy(u32_t *dest, const u32_t *src) {
    dest->bytes[0] = src->bytes[0];
    dest->bytes[1] = src->bytes[1];
    dest->bytes[2] = src->bytes[2];
    dest->bytes[3] = src->bytes[3];
}

// Compare u32_t values (returns -1 if a < b, 0 if a == b, 1 if a > b)
__device__ static inline int u32_cmp(const u32_t *a, const u32_t *b) {
    for (int i = 3; i >= 0; i--) {
        if (a->bytes[i] < b->bytes[i]) return -1;
        if (a->bytes[i] > b->bytes[i]) return 1;
    }
    return 0;
}

// Check if u32_t is zero
__device__ static inline bool u32_is_zero(const u32_t *a) {
    return (a->bytes[0] | a->bytes[1] | a->bytes[2] | a->bytes[3]) == 0;
}

// Ripple carry addition: a = a + b, returns carry
__device__ static inline uint8_t u32_add(u32_t *a, const u32_t *b) {
    uint16_t carry = 0;
    for (int i = 0; i < 4; i++) {
        uint16_t sum = (uint16_t)a->bytes[i] + (uint16_t)b->bytes[i] + carry;
        a->bytes[i] = (uint8_t)(sum & 0xFF);
        carry = sum >> 8;
    }
    return (uint8_t)carry;
}

// Ripple carry subtraction: a = a - b, returns borrow
__device__ static inline uint8_t u32_sub(u32_t *a, const u32_t *b) {
    uint16_t borrow = 0;
    for (int i = 0; i < 4; i++) {
        uint16_t diff = (uint16_t)a->bytes[i] - (uint16_t)b->bytes[i] - borrow;
        a->bytes[i] = (uint8_t)(diff & 0xFF);
        borrow = (diff >> 8) & 1;
    }
    return (uint8_t)borrow;
}

// Bitwise AND
__device__ static inline void u32_and(u32_t *a, const u32_t *b) {
    a->bytes[0] &= b->bytes[0];
    a->bytes[1] &= b->bytes[1];
    a->bytes[2] &= b->bytes[2];
    a->bytes[3] &= b->bytes[3];
}

// Bitwise OR
__device__ static inline void u32_or(u32_t *a, const u32_t *b) {
    a->bytes[0] |= b->bytes[0];
    a->bytes[1] |= b->bytes[1];
    a->bytes[2] |= b->bytes[2];
    a->bytes[3] |= b->bytes[3];
}

// Bitwise XOR
__device__ static inline void u32_xor(u32_t *a, const u32_t *b) {
    a->bytes[0] ^= b->bytes[0];
    a->bytes[1] ^= b->bytes[1];
    a->bytes[2] ^= b->bytes[2];
    a->bytes[3] ^= b->bytes[3];
}

// Left shift by n bits (n < 32)
__device__ static inline void u32_shl(u32_t *a, unsigned int n) {
    if (n >= 32) {
        u32_zero(a);
        return;
    }
    if (n == 0) return;

    if (n >= 8) {
        // Shift by full bytes first
        int byte_shift = n / 8;
        for (int i = 3; i >= byte_shift; i--) {
            a->bytes[i] = a->bytes[i - byte_shift];
        }
        for (int i = byte_shift - 1; i >= 0; i--) {
            a->bytes[i] = 0;
        }
        n %= 8;
    }

    if (n > 0) {
        // Bit-level shift
        uint8_t carry = 0;
        for (int i = 0; i < 4; i++) {
            uint8_t new_carry = a->bytes[i] >> (8 - n);
            a->bytes[i] = (a->bytes[i] << n) | carry;
            carry = new_carry;
        }
    }
}

// Right shift by n bits (n < 32), returns shifted-out bits for sticky
__device__ static inline uint8_t u32_shr(u32_t *a, unsigned int n) {
    if (n >= 32) {
        bool was_zero = u32_is_zero(a);
        u32_zero(a);
        return was_zero ? 0 : 1;
    }
    if (n == 0) return 0;

    uint8_t sticky = 0;

    if (n >= 8) {
        // Check for sticky bits in shifted-out bytes
        int byte_shift = n / 8;
        for (int i = 0; i < byte_shift; i++) {
            if (a->bytes[i] != 0) sticky = 1;
        }
        // Shift by full bytes
        for (int i = 0; i < 4 - byte_shift; i++) {
            a->bytes[i] = a->bytes[i + byte_shift];
        }
        for (int i = 4 - byte_shift; i < 4; i++) {
            a->bytes[i] = 0;
        }
        n %= 8;
    }

    if (n > 0) {
        // Check for sticky bits in the bit-level shift
        for (int i = 0; i < 4; i++) {
            if ((a->bytes[i] & ((1 << n) - 1)) != 0) {
                sticky = 1;
                break;
            }
        }
        // Bit-level shift
        uint8_t carry = 0;
        for (int i = 3; i >= 0; i--) {
            uint8_t new_carry = a->bytes[i] & ((1 << n) - 1);
            a->bytes[i] = (a->bytes[i] >> n) | (carry << (8 - n));
            carry = new_carry;
        }
    }

    return sticky;
}

// Count leading zeros
__device__ static inline int u32_clz(const u32_t *a) {
    for (int byte_idx = 3; byte_idx >= 0; byte_idx--) {
        if (a->bytes[byte_idx] != 0) {
            uint8_t byte = a->bytes[byte_idx];
            int clz_in_byte = 0;
            for (int bit = 7; bit >= 0; bit--) {
                if (byte & (1 << bit)) break;
                clz_in_byte++;
            }
            return (3 - byte_idx) * 8 + clz_in_byte;
        }
    }
    return 32;
}

// IEEE-754 single precision operations
__device__ static inline u32_t toRep(fp_t x) {
    u32_t result;
    union { fp_t f; uint32_t i; } rep = {.f = x};
    u32_from_u32(&result, rep.i);
    return result;
}

__device__ static inline fp_t fromRep(const u32_t *x) {
    union { fp_t f; uint32_t i; } rep = {.i = u32_to_u32(x)};
    return rep.f;
}

// IEEE-754 constants as u32_t
static const u32_t IMPLICIT_BIT = {{0, 0, 0x80, 0}};  // 1 << 23
static const u32_t SIGNIFICAND_MASK = {{0xFF, 0xFF, 0x7F, 0}};  // (1 << 23) - 1
static const u32_t SIGN_BIT = {{0, 0, 0, 0x80}};  // 1 << 31
static const u32_t ABS_MASK = {{0xFF, 0xFF, 0xFF, 0x7F}};  // SIGN_BIT - 1
static const u32_t EXPONENT_MASK = {{0, 0, 0x80, 0x7F}};  // ABS_MASK ^ SIGNIFICAND_MASK
static const u32_t INF_REP = {{0, 0, 0x80, 0x7F}};  // EXPONENT_MASK
static const u32_t QUIET_BIT = {{0, 0, 0x40, 0}};  // IMPLICIT_BIT >> 1
static const u32_t QNAN_REP = {{0, 0, 0xC0, 0x7F}};  // EXPONENT_MASK | QUIET_BIT
static const u32_t ONE_REP = {{0, 0, 0, 0x3F}};  // exponentBias << 23

// Helper to create u32_t constant
__device__ static inline void u32_set_const(u32_t *dest, uint32_t val) {
    u32_from_u32(dest, val);
}

// Normalize denormal significand, returns adjusted exponent
__device__ static inline int u32_normalize(u32_t *significand) {
    u32_t implicit_bit_shifted;
    u32_set_const(&implicit_bit_shifted, 1 << SIGNIFICAND_BITS);
    int implicit_clz = u32_clz(&implicit_bit_shifted);
    int sig_clz = u32_clz(significand);
    int shift = sig_clz - implicit_clz;
    u32_shl(significand, shift);
    return 1 - shift;
}

// Main floating-point addition function
__device__ static inline fp_t __addXf4__(fp_t a, fp_t b) {
    u32_t aRep = toRep(a);
    u32_t bRep = toRep(b);

    u32_t aAbs, bAbs;
    u32_copy(&aAbs, &aRep);
    u32_copy(&bAbs, &bRep);
    u32_and(&aAbs, &ABS_MASK);
    u32_and(&bAbs, &ABS_MASK);

    // Check for special cases (infinity, NaN, zero)
    u32_t temp1, temp2, const_one, inf_minus_one;
    u32_set_const(&const_one, 1);
    u32_set_const(&inf_minus_one, 1);

    u32_copy(&temp1, &aAbs);
    u32_copy(&temp2, &const_one);
    u32_sub(&temp1, &temp2);  // aAbs - 1

    u32_copy(&temp2, &INF_REP);
    u32_sub(&temp2, &inf_minus_one);  // infRep - 1

    bool aSpecial = u32_cmp(&temp1, &temp2) >= 0;

    u32_copy(&temp1, &bAbs);
    u32_copy(&temp2, &const_one);
    u32_sub(&temp1, &temp2);  // bAbs - 1

    u32_copy(&temp2, &INF_REP);
    u32_copy(&inf_minus_one, &const_one);
    u32_sub(&temp2, &inf_minus_one);  // infRep - 1

    bool bSpecial = u32_cmp(&temp1, &temp2) >= 0;

    if (aSpecial || bSpecial) {
        // NaN handling
        if (u32_cmp(&aAbs, &INF_REP) > 0) {
            u32_t result = toRep(a);
            u32_or(&result, &QUIET_BIT);
            return fromRep(&result);
        }
        if (u32_cmp(&bAbs, &INF_REP) > 0) {
            u32_t result = toRep(b);
            u32_or(&result, &QUIET_BIT);
            return fromRep(&result);
        }

        // Infinity handling
        if (u32_cmp(&aAbs, &INF_REP) == 0) {
            u32_t aRepCopy = toRep(a);
            u32_t bRepCopy = toRep(b);
            u32_xor(&aRepCopy, &bRepCopy);
            u32_and(&aRepCopy, &SIGN_BIT);
            if (!u32_is_zero(&aRepCopy)) {
                return fromRep(&QNAN_REP);
            } else {
                return a;
            }
        }

        if (u32_cmp(&bAbs, &INF_REP) == 0) {
            return b;
        }

        // Zero handling
        if (u32_is_zero(&aAbs)) {
            if (u32_is_zero(&bAbs)) {
                u32_t aRepCopy = toRep(a);
                u32_t bRepCopy = toRep(b);
                u32_and(&aRepCopy, &bRepCopy);
                return fromRep(&aRepCopy);
            } else {
                return b;
            }
        }

        if (u32_is_zero(&bAbs)) {
            return a;
        }
    }

    // Swap if necessary so that a has the larger absolute value
    if (u32_cmp(&bAbs, &aAbs) > 0) {
        u32_t temp;
        u32_copy(&temp, &aRep);
        u32_copy(&aRep, &bRep);
        u32_copy(&bRep, &temp);
    }

    // Extract exponent and significand
    u32_t aExp, bExp, aSig, bSig, max_exp_mask;
    u32_set_const(&max_exp_mask, MAX_EXPONENT);

    u32_copy(&aExp, &aRep);
    u32_shr(&aExp, SIGNIFICAND_BITS);
    u32_and(&aExp, &max_exp_mask);

    u32_copy(&bExp, &bRep);
    u32_shr(&bExp, SIGNIFICAND_BITS);
    u32_and(&bExp, &max_exp_mask);

    u32_copy(&aSig, &aRep);
    u32_and(&aSig, &SIGNIFICAND_MASK);

    u32_copy(&bSig, &bRep);
    u32_and(&bSig, &SIGNIFICAND_MASK);

    // Normalize denormals
    int aExponent = u32_to_u32(&aExp);
    int bExponent = u32_to_u32(&bExp);

    if (aExponent == 0) {
        aExponent = u32_normalize(&aSig);
    }
    if (bExponent == 0) {
        bExponent = u32_normalize(&bSig);
    }

    // Determine result sign and operation
    u32_t resultSign;
    u32_copy(&resultSign, &aRep);
    u32_and(&resultSign, &SIGN_BIT);

    u32_t aRepCopy, bRepCopy;
    u32_copy(&aRepCopy, &aRep);
    u32_copy(&bRepCopy, &bRep);
    u32_xor(&aRepCopy, &bRepCopy);
    u32_and(&aRepCopy, &SIGN_BIT);
    bool subtraction = !u32_is_zero(&aRepCopy);

    // Set implicit bit and add guard bits
    u32_or(&aSig, &IMPLICIT_BIT);
    u32_shl(&aSig, 3);

    u32_or(&bSig, &IMPLICIT_BIT);
    u32_shl(&bSig, 3);

    // Align significands
    unsigned int align = (unsigned int)(aExponent - bExponent);
    if (align > 0) {
        if (align < TYPE_WIDTH) {
            uint8_t sticky = u32_shr(&bSig, align);
            if (sticky) {
                u32_t one;
                u32_set_const(&one, 1);
                u32_or(&bSig, &one);
            }
        } else {
            u32_zero(&bSig);
            u32_from_u32(&bSig, 1);  // Set sticky bit
        }
    }

    // Perform addition or subtraction
    if (subtraction) {
        u32_sub(&aSig, &bSig);

        // Check for zero result
        if (u32_is_zero(&aSig)) {
            u32_t zero;
            u32_set_const(&zero, 0);
            return fromRep(&zero);
        }

        // Handle partial cancellation
        u32_t implicitShifted = IMPLICIT_BIT;
        u32_shl(&implicitShifted, 3);
        if (u32_cmp(&aSig, &implicitShifted) < 0) {
            int sigClz = u32_clz(&aSig);
            int impClz = u32_clz(&implicitShifted);
            int shift = sigClz - impClz;
            u32_shl(&aSig, shift);
            aExponent -= shift;
        }
    } else {
        u32_add(&aSig, &bSig);

        // Handle overflow
        u32_t implicitShifted = IMPLICIT_BIT;
        u32_shl(&implicitShifted, 4);
        u32_t temp;
        u32_copy(&temp, &aSig);
        u32_and(&temp, &implicitShifted);
        if (!u32_is_zero(&temp)) {
            u32_t one;
            u32_set_const(&one, 1);
            u32_and(&one, &aSig);
            uint8_t sticky = !u32_is_zero(&one) ? 1 : 0;
            u32_shr(&aSig, 1);
            if (sticky) {
                u32_t stickyBit;
                u32_set_const(&stickyBit, 1);
                u32_or(&aSig, &stickyBit);
            }
            aExponent += 1;
        }
    }

    // Handle exponent overflow
    if (aExponent >= MAX_EXPONENT) {
        u32_t result = INF_REP;
        u32_or(&result, &resultSign);
        return fromRep(&result);
    }

    // Handle denormal result
    if (aExponent <= 0) {
        int shift = 1 - aExponent;
        uint8_t sticky = u32_shr(&aSig, shift);
        if (sticky) {
            u32_t stickyBit;
            u32_set_const(&stickyBit, 1);
            u32_or(&aSig, &stickyBit);
        }
        aExponent = 0;
    }

    // Extract round/guard/sticky bits
    u32_t roundGuardSticky, mask_7;
    u32_set_const(&mask_7, 0x7);
    u32_copy(&roundGuardSticky, &aSig);
    u32_and(&roundGuardSticky, &mask_7);

    // Shift significand into place
    u32_t result;
    u32_copy(&result, &aSig);
    u32_shr(&result, 3);
    u32_and(&result, &SIGNIFICAND_MASK);

    // Insert exponent
    u32_t expShifted;
    u32_set_const(&expShifted, aExponent);
    u32_shl(&expShifted, SIGNIFICAND_BITS);
    u32_or(&result, &expShifted);

    // Insert sign
    u32_or(&result, &resultSign);

    // Perform rounding (round to nearest, ties to even)
    u32_t rgs = roundGuardSticky;
    u32_t four;
    u32_set_const(&four, 4);
    if (u32_cmp(&rgs, &four) > 0) {
        u32_t one;
        u32_set_const(&one, 1);
        u32_add(&result, &one);
    } else if (u32_cmp(&rgs, &four) == 0) {
        u32_t one_rounding;
        u32_set_const(&one_rounding, 1);
        u32_t resultLsb;
        u32_copy(&resultLsb, &result);
        u32_and(&resultLsb, &one_rounding);
        u32_add(&result, &resultLsb);
    }

    return fromRep(&result);
}
