#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
// In theory I think this comes from <climits.h>
#define CHAR_BIT 8

typedef uint32_t half_rep_t;
typedef uint64_t rep_t;
typedef int64_t srep_t;
typedef double fp_t;
#define HALF_REP_C UINT32_C
#define REP_C UINT64_C
#define significandBits 52

static inline int rep_clz(rep_t a) { return __builtin_clzll(a); }

#define loWord(a) (a & 0xffffffffU)
#define hiWord(a) (a >> 32)

#define typeWidth (sizeof(rep_t) * CHAR_BIT)

static __inline rep_t toRep(fp_t x) { //double x
  const union {
    fp_t f; //double f
    rep_t i; //u64 -> so bit cast to double
  } rep = {.f = x};
  return rep.i;
}

static __inline fp_t fromRep(rep_t x) {
  const union {
    fp_t f;
    rep_t i;
  } rep = {.i = x};
  return rep.f;
}

#define exponentBits (typeWidth - significandBits - 1)
#define maxExponent ((1 << exponentBits) - 1)
#define exponentBias (maxExponent >> 1)

#define implicitBit (REP_C(1) << significandBits)
#define significandMask (implicitBit - 1U)
#define signBit (REP_C(1) << (significandBits + exponentBits))
#define absMask (signBit - 1U)
#define exponentMask (absMask ^ significandMask)
#define oneRep ((rep_t)exponentBias << significandBits)
#define infRep exponentMask
#define quietBit (implicitBit >> 1)
#define qnanRep (exponentMask | quietBit)

static __inline int normalize(rep_t *significand) {
  const int shift = rep_clz(*significand) - rep_clz(implicitBit);
  *significand <<= shift;
  return 1 - shift;
}

static __inline fp_t __addXf3__(fp_t a, fp_t b) {
  rep_t aRep = toRep(a); // bitcast to u64 from f64
  rep_t bRep = toRep(b);
  const rep_t aAbs = aRep & absMask; // absolute of rep
  const rep_t bAbs = bRep & absMask;

  // Detect if a or b is zero, infinity, or NaN.
  // NOTE: (AA) What if we remove all of this
  if (aAbs - REP_C(1) >= infRep - REP_C(1) ||
      bAbs - REP_C(1) >= infRep - REP_C(1)) {
    // NaN + anything = qNaN
    if (aAbs > infRep)
      return fromRep(toRep(a) | quietBit);
    // anything + NaN = qNaN
    if (bAbs > infRep)
      return fromRep(toRep(b) | quietBit);

    if (aAbs == infRep) {
      // +/-infinity + -/+infinity = qNaN
      if ((toRep(a) ^ toRep(b)) == signBit)
        return fromRep(qnanRep);
      // +/-infinity + anything remaining = +/- infinity
      else
        return a;
    }

    // anything remaining + +/-infinity = +/-infinity
    if (bAbs == infRep)
      return b;

    // zero + anything = anything
    if (!aAbs) {
      // We need to get the sign right for zero + zero.
      if (!bAbs)
        return fromRep(toRep(a) & toRep(b));
      else
        return b;
    }

    // anything + zero = anything
    if (!bAbs)
      return a;
  }

  // Swap a and b if necessary so that a has the larger absolute value.
  if (bAbs > aAbs) {
    const rep_t temp = aRep;
    aRep = bRep;
    bRep = temp;
  }

  // Extract the exponent and significand from the (possibly swapped) a and b.
  int aExponent = aRep >> significandBits & maxExponent;
  int bExponent = bRep >> significandBits & maxExponent;
  rep_t aSignificand = aRep & significandMask;
  rep_t bSignificand = bRep & significandMask;

  // Normalize any denormals, and adjust the exponent accordingly.
  // NOTE: For fluid dynamics we can probably ignore denormals, since
  //  they are for 1.1754943-38 and smaller. Clamp to zero
  if (aExponent == 0)
    aExponent = normalize(&aSignificand);
  if (bExponent == 0)
    bExponent = normalize(&bSignificand);

  // The sign of the result is the sign of the larger operand, a.  If they
  // have opposite signs, we are performing a subtraction.  Otherwise, we
  // perform addition.
  const rep_t resultSign = aRep & signBit;
  const bool subtraction = (aRep ^ bRep) & signBit;

  // Shift the significands to give us round, guard and sticky, and set the
  // implicit significand bit.  If we fell through from the denormal path it
  // was already set by normalize( ), but setting it twice won't hurt
  // anything.
  aSignificand = (aSignificand | implicitBit) << 3;
  bSignificand = (bSignificand | implicitBit) << 3;

  // Shift the significand of b by the difference in exponents, with a sticky
  // bottom bit to get rounding correct.
  const unsigned int align = (unsigned int)(aExponent - bExponent);
  if (align) {
    if (align < typeWidth) {
      const bool sticky = (bSignificand << (typeWidth - align)) != 0;
      bSignificand = bSignificand >> align | sticky;
    } else {
      bSignificand = 1; // Set the sticky bit.  b is known to be non-zero.
    }
  }
  // NOTE: (AA) this can be a bit operation methinks
  if (subtraction) {
    aSignificand -= bSignificand;
    // If a == -b, return +zero.
    if (aSignificand == 0)
      return fromRep(0);

    // If partial cancellation occured, we need to left-shift the result
    // and adjust the exponent.
    if (aSignificand < implicitBit << 3) {
      const int shift = rep_clz(aSignificand) - rep_clz(implicitBit << 3);
      aSignificand <<= shift;
      aExponent -= shift;
    }
  } else /* addition */ {
    aSignificand += bSignificand;

    // If the addition carried up, we need to right-shift the result and
    // adjust the exponent.
    if (aSignificand & implicitBit << 4) {
      const bool sticky = aSignificand & 1;
      aSignificand = aSignificand >> 1 | sticky;
      aExponent += 1;
    }
  }

  // If we have overflowed the type, return +/- infinity.
  // FIXME: (AA) We could have a simplifying assumption
  //  to assume that it never overflows. 'cause if you 
  //  overflow in physics, something is wrong
  if (aExponent >= maxExponent)
    return fromRep(infRep | resultSign);

  // FIXME: (AA) Once again, we could simplify this maybe
  if (aExponent <= 0) {
    // The result is denormal before rounding.  The exponent is zero and we
    // need to shift the significand.
    const int shift = 1 - aExponent;
    const bool sticky = (aSignificand << (typeWidth - shift)) != 0;
    aSignificand = aSignificand >> shift | sticky;
    aExponent = 0;
  }

  // Low three bits are round, guard, and sticky.
  const int roundGuardSticky = aSignificand & 0x7;

  // Shift the significand into place, and mask off the implicit bit.
  rep_t result = aSignificand >> 3 & significandMask;

  // Insert the exponent and sign.
  result |= (rep_t)aExponent << significandBits;
  result |= resultSign;

  // Perform the final rounding.  The result may overflow to infinity, but
  // that is the correct result in that case.
  // NOTE: (AA) We will always round to the nearest

  // switch (__fe_getround()) {
  // case CRT_FE_TONEAREST:
  if (roundGuardSticky > 0x4)
    result++;
  if (roundGuardSticky == 0x4)
    result += result & 1;
    // break;
  // case CRT_FE_DOWNWARD:
  //   if (resultSign && roundGuardSticky) result++;
  //   break;
  // case CRT_FE_UPWARD:
  //   if (!resultSign && roundGuardSticky) result++;
  //   break;
  // case CRT_FE_TOWARDZERO:
  //   break;
  // }
  // if (roundGuardSticky)
  //   __fe_raise_inexact();
  return fromRep(result);
}

int main() {
  double a = 2.0;
  double b = 3.0;

  double c = __addXf3__(a, b);

  printf("From emulation: %f\n", c);
  printf("Expected: %f\n", a + b);
  return 0;
}
