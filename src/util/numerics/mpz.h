/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstddef>
#include <gmp.h>
#include <string>
#include <iostream>
#include <limits>
#include "util/debug.h"
#include "util/serializer.h"

namespace lean {
class mpq;

/**
   \brief Wrapper for GMP integers
*/
class mpz {
    friend class mpq;
    friend class mpfp;
    mpz_t m_val;
    mpz(__mpz_struct const * v) { mpz_init_set(m_val, v); }
public:
    mpz() { mpz_init(m_val); }
    explicit mpz(char const * v) { mpz_init_set_str(m_val, const_cast<char*>(v), 10); }
    explicit mpz(unsigned long int v) { mpz_init_set_ui(m_val, v); }
    explicit mpz(long int v) { mpz_init_set_si(m_val, v); }
    explicit mpz(unsigned int v) { mpz_init_set_ui(m_val, v); }
    explicit mpz(int v) { mpz_init_set_si(m_val, v); }
    explicit mpz(uint64 v);
    explicit mpz(int64 v);
    explicit mpz(double v) { mpz_init_set_d(m_val, v); }
    mpz(mpz const & s) { mpz_init_set(m_val, s.m_val); }
    mpz(mpz && s):mpz() { mpz_swap(m_val, s.m_val); }
    ~mpz() { mpz_clear(m_val); }

    friend void swap(mpz & a, mpz & b) { mpz_swap(a.m_val, b.m_val); }

    unsigned hash() const { return static_cast<unsigned>(mpz_get_si(m_val)); }

    int sgn() const { return mpz_sgn(m_val); }
    friend int sgn(mpz const & a) { return a.sgn(); }
    bool is_pos() const { return sgn() > 0; }
    bool is_neg() const { return sgn() < 0; }
    bool is_zero() const { return sgn() == 0; }
    bool is_nonpos() const { return !is_pos(); }
    bool is_nonneg() const { return !is_neg(); }

    void neg() { mpz_neg(m_val, m_val); }
    friend mpz neg(mpz a) { a.neg(); return a; }

    void abs() { mpz_abs(m_val, m_val); }
    friend mpz abs(mpz a) { a.abs(); return a; }

    bool even() const { return mpz_even_p(m_val) != 0; }
    bool odd() const { return !even(); }

    template <typename T> bool is() const = delete;

    explicit operator long int() const;
    explicit operator unsigned long int() const;
    explicit operator int() const;
    explicit operator unsigned int() const;
    explicit operator long long int() const;
    explicit operator unsigned long long int() const;

    // not a cast operator, to match `mpz`
    double get_double() const { return mpz_get_d(m_val); }

    mpz & operator=(mpz const & v) { mpz_set(m_val, v.m_val); return *this; }
    mpz & operator=(mpz && v) { swap(*this, v); return *this; }
    mpz & operator=(char const * v) { mpz_set_str(m_val, v, 10); return *this; }
    mpz & operator=(unsigned long int v) { mpz_set_ui(m_val, v); return *this; }
    mpz & operator=(long int v) { mpz_set_si(m_val, v); return *this; }
    mpz & operator=(unsigned int v) { return operator=(static_cast<unsigned long int>(v)); }
    mpz & operator=(int v) { return operator=(static_cast<long int>(v)); }
    mpz & operator=(double v) { mpz_set_d(m_val, v); return *this; }

    friend int cmp(mpz const & a, mpz const & b) { return mpz_cmp(a.m_val, b.m_val); }
    friend int cmp(mpz const & a, unsigned b) { return mpz_cmp_ui(a.m_val, b); }
    friend int cmp(mpz const & a, int b) { return mpz_cmp_si(a.m_val, b); }

    friend bool operator<(mpz const & a, mpz const & b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, unsigned b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, int b) { return cmp(a, b) < 0; }
    friend bool operator<(unsigned a, mpz const & b) { return cmp(b, a) > 0; }
    friend bool operator<(int a, mpz const & b) { return cmp(b, a) > 0; }

    friend bool operator>(mpz const & a, mpz const & b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, unsigned b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, int b) { return cmp(a, b) > 0; }
    friend bool operator>(unsigned a, mpz const & b) { return cmp(b, a) < 0; }
    friend bool operator>(int a, mpz const & b) { return cmp(b, a) < 0; }

    friend bool operator<=(mpz const & a, mpz const & b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, unsigned b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, int b) { return cmp(a, b) <= 0; }
    friend bool operator<=(unsigned a, mpz const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(int a, mpz const & b) { return cmp(b, a) >= 0; }

    friend bool operator>=(mpz const & a, mpz const & b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, unsigned b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, int b) { return cmp(a, b) >= 0; }
    friend bool operator>=(unsigned a, mpz const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(int a, mpz const & b) { return cmp(b, a) <= 0; }

    friend bool operator==(mpz const & a, mpz const & b) { return cmp(a, b) == 0; }
    friend bool operator==(mpz const & a, unsigned b) { return cmp(a, b) == 0; }
    friend bool operator==(mpz const & a, int b) { return cmp(a, b) == 0; }
    friend bool operator==(unsigned a, mpz const & b) { return cmp(b, a) == 0; }
    friend bool operator==(int a, mpz const & b) { return cmp(b, a) == 0; }

    friend bool operator!=(mpz const & a, mpz const & b) { return cmp(a, b) != 0; }
    friend bool operator!=(mpz const & a, unsigned b) { return cmp(a, b) != 0; }
    friend bool operator!=(mpz const & a, int b) { return cmp(a, b) != 0; }
    friend bool operator!=(unsigned a, mpz const & b) { return cmp(b, a) != 0; }
    friend bool operator!=(int a, mpz const & b) { return cmp(b, a) != 0; }

    mpz & operator+=(mpz const & o) { mpz_add(m_val, m_val, o.m_val); return *this; }
    mpz & operator+=(unsigned u) { mpz_add_ui(m_val, m_val, u); return *this; }
    mpz & operator+=(int u) { if (u >= 0) mpz_add_ui(m_val, m_val, u); else mpz_sub_ui(m_val, m_val, -u); return *this; }

    mpz & operator-=(mpz const & o) { mpz_sub(m_val, m_val, o.m_val); return *this; }
    mpz & operator-=(unsigned u) { mpz_sub_ui(m_val, m_val, u); return *this; }
    mpz & operator-=(int u) { if (u >= 0) mpz_sub_ui(m_val, m_val, u); else mpz_add_ui(m_val, m_val, -u); return *this; }

    mpz & operator*=(mpz const & o) { mpz_mul(m_val, m_val, o.m_val); return *this; }
    mpz & operator*=(unsigned u) { mpz_mul_ui(m_val, m_val, u); return *this; }
    mpz & operator*=(int u) { mpz_mul_si(m_val, m_val, u); return *this; }

    mpz & operator/=(mpz const & o) { mpz_tdiv_q(m_val, m_val, o.m_val); return *this; }
    mpz & operator/=(unsigned u) { mpz_tdiv_q_ui(m_val, m_val, u); return *this; }

    friend mpz rem(mpz const & a, mpz const & b) { mpz r; mpz_tdiv_r(r.m_val, a.m_val, b.m_val); return r; }
    mpz & operator%=(mpz const & o) { mpz r(*this % o); mpz_swap(m_val, r.m_val); return *this; }

    friend mpz operator+(mpz a, mpz const & b) { return a += b; }
    friend mpz operator+(mpz a, unsigned b)  { return a += b; }
    friend mpz operator+(mpz a, int b)  { return a += b; }
    friend mpz operator+(unsigned a, mpz b) { return b += a; }
    friend mpz operator+(int a, mpz b) { return b += a; }

    friend mpz operator-(mpz a, mpz const & b) { return a -= b; }
    friend mpz operator-(mpz a, unsigned b) { return a -= b; }
    friend mpz operator-(mpz a, int b) { return a -= b; }
    friend mpz operator-(unsigned a, mpz b) { b.neg(); return b += a; }
    friend mpz operator-(int a, mpz b) { b.neg(); return b += a; }

    friend mpz operator*(mpz a, mpz const & b) { return a *= b; }
    friend mpz operator*(mpz a, unsigned b) { return a *= b; }
    friend mpz operator*(mpz a, int b) { return a *= b; }
    friend mpz operator*(unsigned a, mpz b) { return b *= a; }
    friend mpz operator*(int a, mpz b) { return b *= a; }

    friend mpz operator/(mpz a, mpz const & b) { return a /= b; }
    friend mpz operator/(mpz a, unsigned b) { return a /= b; }
    friend mpz operator/(mpz a, int b) { return a /= b; }
    friend mpz operator/(unsigned a, mpz const & b) { mpz r(a); return r /= b; }
    friend mpz operator/(int a, mpz const & b) { mpz r(a); return r /= b; }

    friend mpz operator%(mpz const & a, mpz const & b);

    mpz & operator++() { return operator+=(1); }
    mpz operator++(int) { mpz r(*this); ++(*this); return r; }

    mpz & operator--() { return operator-=(1); }
    mpz operator--(int) { mpz r(*this); --(*this); return r; }

    mpz & operator&=(mpz const & o) { mpz_and(m_val, m_val, o.m_val); return *this; }
    mpz & operator|=(mpz const & o) { mpz_ior(m_val, m_val, o.m_val); return *this; }
    mpz & operator^=(mpz const & o) { mpz_xor(m_val, m_val, o.m_val); return *this; }
    void comp() { mpz_com(m_val, m_val); }

    friend mpz operator&(mpz a, mpz const & b) { return a &= b; }
    friend mpz operator|(mpz a, mpz const & b) { return a |= b; }
    friend mpz operator^(mpz a, mpz const & b) { return a ^= b; }
    friend mpz operator~(mpz a) { a.comp(); return a; }

    bool test_bit(size_t bit) const { return mpz_tstbit(m_val, bit) != 0; }

    // this <- this + a*b
    void addmul(mpz const & a, mpz const & b) { mpz_addmul(m_val, a.m_val, b.m_val); }
    // this <- this - a*b
    void submul(mpz const & a, mpz const & b) { mpz_submul(m_val, a.m_val, b.m_val); }

    // a <- b * 2^k
    friend void mul2k(mpz & a, mpz const & b, unsigned k) { mpz_mul_2exp(a.m_val, b.m_val, k); }
    // a <- b / 2^k
    friend void div2k(mpz & a, mpz const & b, unsigned k) { mpz_tdiv_q_2exp(a.m_val, b.m_val, k); }

    /**
       \brief Return the position of the most significant bit.
       Return 0 if the number is negative
    */
    unsigned log2() const;

    /**
       \brief log2(-n)
       Return 0 if the number is nonegative
    */
    unsigned mlog2() const;

    bool perfect_square() const { return mpz_perfect_square_p(m_val); }

    bool is_power_of_two() const { return is_pos() && mpz_popcount(m_val) == 1; }
    bool is_power_of_two(unsigned & shift) const;
    /**
       \brief Return largest k s.t. n is a multiple of 2^k
    */
    unsigned power_of_two_multiple() const { return mpz_scan1(m_val, 0); }

    friend void power(mpz & a, mpz const & b, unsigned k) { mpz_pow_ui(a.m_val, b.m_val, k); }
    friend void _power(mpz & a, mpz const & b, unsigned k) { power(a, b, k); }
    friend mpz pow(mpz a, unsigned k) { power(a, a, k); return a; }

    friend void rootrem(mpz & root, mpz & rem, mpz const & a, unsigned k) { mpz_rootrem(root.m_val, rem.m_val, a.m_val, k); }
    // root <- a^{1/k}, return true iff the result is an integer
    friend bool root(mpz & root, mpz const & a, unsigned k);
    friend mpz root(mpz const & a, unsigned k) { mpz r; root(r, a, k); return r; }

    friend void gcd(mpz & g, mpz const & a, mpz const & b) { mpz_gcd(g.m_val, a.m_val, b.m_val); }
    friend mpz gcd(mpz const & a, mpz const & b) { mpz r; gcd(r, a, b); return r; }
    friend void gcdext(mpz & g, mpz & s, mpz & t, mpz const & a, mpz const & b) { mpz_gcdext(g.m_val, s.m_val, t.m_val, a.m_val, b.m_val); }
    friend void lcm(mpz & l, mpz const & a, mpz const & b) { mpz_lcm(l.m_val, a.m_val, b.m_val); }
    friend mpz lcm(mpz const & a, mpz const & b) { mpz l; lcm(l, a, b); return l; }

    friend std::ostream & operator<<(std::ostream & out, mpz const & v);

    std::string to_string() const;
};

template<> inline bool mpz::is<int>()               const { return mpz_fits_sint_p(m_val) != 0; }
template<> inline bool mpz::is<unsigned int>()      const { return mpz_fits_uint_p(m_val) != 0; }
template<> inline bool mpz::is<long int>()          const { return mpz_fits_slong_p(m_val) != 0; }
template<> inline bool mpz::is<unsigned long int>() const { return mpz_fits_ulong_p(m_val) != 0; }
// TODO(eric-wieser): these could be faster, but gmp has no API for us
template<> inline bool mpz::is<long long>() const {
    return mpz(std::numeric_limits<long long>::min()) <= *this && *this <= mpz(std::numeric_limits<long long>::max()); }
template<> inline bool mpz::is<unsigned long long>() const {
    return mpz(std::numeric_limits<unsigned long long>::min()) <= *this && *this <= mpz(std::numeric_limits<unsigned long long>::max()); }

// we can't define these until the `is` specializations are declared
inline mpz::operator long int()          const { lean_assert(is<long int>());          return mpz_get_si(m_val); }
inline mpz::operator unsigned long int() const { lean_assert(is<unsigned long int>()); return mpz_get_ui(m_val); }
inline mpz::operator int()               const { lean_assert(is<int>());          return static_cast<long>(operator long int()); }
inline mpz::operator unsigned int()      const { lean_assert(is<unsigned int>()); return static_cast<unsigned>(operator unsigned long int()); }

struct mpz_cmp_fn {
    int operator()(mpz const & v1, mpz const & v2) const { return cmp(v1, v2); }
};


serializer & operator<<(serializer & s, mpz const & n);
mpz read_mpz(deserializer & d);
inline deserializer & operator>>(deserializer & d, mpz & n) { n = read_mpz(d); return d; }

}

template<> struct std::numeric_limits<lean::mpz> {
    static constexpr bool is_specialized = true;
    static constexpr bool is_signed = true;
    static constexpr bool is_integer = true;
    static constexpr bool is_exact = true;
    static constexpr bool has_infinity = false;
    static constexpr bool has_quiet_NaN = false;
    static constexpr bool has_signaling_NaN = false;
    static constexpr std::float_denorm_style has_denorm = std::denorm_absent;
    static constexpr bool has_denorm_loss = false;
    static constexpr std::float_round_style round_style = std::round_toward_zero;
    static constexpr bool is_iec559 = false;
    static constexpr bool is_bounded = false;
    static constexpr bool is_modulo = false;

    // these fields don't make sense for mpz
    // digits
    // digits10
    // max_digits10
    // radix

    // these are copied from the values for integers
    static constexpr int min_exponent = 0;
    static constexpr int min_exponent10 = 0;
    static constexpr int max_exponent = 0;
    static constexpr int max_exponent10 = 0;

    static constexpr bool traps = true;
    static constexpr bool tinyness_before = false;
};
