/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/hash.h"
#include <string>

namespace lean {

void mix(unsigned & a, unsigned & b, unsigned & c) {
    a -= b; a -= c; a ^= (c >> 13);
    b -= c; b -= a; b ^= (a << 8);
    c -= a; c -= b; c ^= (b >> 13);
    a -= b; a -= c; a ^= (c >> 12);
    b -= c; b -= a; b ^= (a << 16);
    c -= a; c -= b; c ^= (b >> 5);
    a -= b; a -= c; a ^= (c >> 3);
    b -= c; b -= a; b ^= (a << 10);
    c -= a; c -= b; c ^= (b >> 15);
}

// Bob Jenkin's hash function.
// http://burtleburtle.net/bob/hash/doobs.html
unsigned hash_str(unsigned length, char const * str, unsigned init_value) {
    unsigned a, b, c, len;

    /* Set up the internal state */
    len = length;
    a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
    c = init_value;      /* the previous hash value */

    /*---------------------------------------- handle most of the key */
    while (len >= 12) {
        a += reinterpret_cast<unsigned const *>(str)[0];
        b += reinterpret_cast<unsigned const *>(str)[1];
        c += reinterpret_cast<unsigned const *>(str)[2];
        mix(a, b, c);
        str += 12; len -= 12;
    }

    /*------------------------------------- handle the last 11 bytes */
    c += length;
    switch (len) {
        /* all the case statements fall through */
    case 11:  c+=((unsigned)str[10] << 24);  /* fall-thru */
    case 10:  c+=((unsigned)str[9] << 16);   /* fall-thru */
    case 9 :  c+=((unsigned)str[8] << 8);    /* fall-thru */
        /* the first byte of c is reserved for the length */
    case 8 :  b+=((unsigned)str[7] << 24);   /* fall-thru */
    case 7 :  b+=((unsigned)str[6] << 16);   /* fall-thru */
    case 6 :  b+=((unsigned)str[5] << 8);    /* fall-thru */
    case 5 :  b+=(unsigned)str[4];           /* fall-thru */
    case 4 :  a+=((unsigned)str[3] << 24);   /* fall-thru */
    case 3 :  a+=((unsigned)str[2] << 16);   /* fall-thru */
    case 2 :  a+=((unsigned)str[1] << 8);    /* fall-thru */
    case 1 :  a+=(unsigned)str[0];
        /* case 0: nothing left to add */
    }
    mix(a, b, c);
    /*-------------------------------------------- report the result */
    return c;
}

unsigned hash_data(std::string const & data) {
    return hash(data.size(), [&] (unsigned i) { return static_cast<unsigned char>(data.data()[i]); });
}


//-----------------------------------------------------------------------------
// MurmurHash2, 64-bit versions, by Austin Appleby
// https://sites.google.com/site/murmurhash/

static uint64_t MurmurHash64A(void const * key, int len, unsigned int seed) {
    const uint64_t m = 0xc6a4a7935bd1e995;
    const int r = 47;

    uint64_t h = seed ^ (len * m);

    const uint64_t * data = (const uint64_t *)key;
    const uint64_t * end = data + (len/8);

    while (data != end) {
        uint64_t k = *data++;

        k *= m;
        k ^= k >> r;
        k *= m;

        h ^= k;
        h *= m;
    }

    const unsigned char * data2 = (const unsigned char *) data;

    switch (len & 7) {
    case 7: h ^= uint64_t(data2[6]) << 48;
    case 6: h ^= uint64_t(data2[5]) << 40;
    case 5: h ^= uint64_t(data2[4]) << 32;
    case 4: h ^= uint64_t(data2[3]) << 24;
    case 3: h ^= uint64_t(data2[2]) << 16;
    case 2: h ^= uint64_t(data2[1]) << 8;
    case 1: h ^= uint64_t(data2[0]);
            h *= m;
    };

    h ^= h >> r;
    h *= m;
    h ^= h >> r;

    return h;
}

uint64 hash64_str(unsigned len, char const * str, uint64 init_value) {
    return MurmurHash64A(str, len, init_value);
}

uint64 hash64_str(std::string const & str, uint64 init_value) {
    return hash64_str(str.length(), str.c_str(), init_value);
}

}
