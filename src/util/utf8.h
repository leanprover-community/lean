/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/buffer.h"
#include "util/optional.h"

namespace lean {
using uchar = unsigned char;

bool is_utf8_next(unsigned char c);
unsigned get_utf8_size(unsigned char c);
size_t utf8_strlen(char const * str);
optional<size_t> utf8_char_pos(char const * str, size_t char_idx);
char const * get_utf8_last_char(char const * str);
std::string utf8_trim(std::string const & s);
unsigned utf8_to_unicode(uchar const * begin, uchar const * end);
inline unsigned utf8_to_unicode(char const * begin, char const * end) {
    return utf8_to_unicode(reinterpret_cast<uchar const *>(begin),
                           reinterpret_cast<uchar const *>(end));
}

/* If `c` is the first byte of an utf-8 encoded unicode scalar value,
   then return `some(n)` where `n` is the number of bytes needed to encode
   the unicode scalar value. Otherwise, return `none` */
optional<unsigned> is_utf8_first_byte(unsigned char c);

/* "Read" next unicode character starting at position i in a string using UTF-8 encoding.
   Return the unicode character and update i. */
unsigned next_utf8_buff(const char *str, size_t len, size_t & i);
unsigned next_utf8(std::string const & str, size_t & i);

/* Decode a UTF-8 encoded string `str` into unicode scalar values */
void utf8_decode(std::string const & str, buffer<unsigned> & out);

/* Push a unicode scalar value into a utf-8 encoded string */
void push_unicode_scalar(std::string & s, unsigned code);

/* Push a unicode scalar value into a utf-8 encoded buffer */
void push_unicode_scalar(buffer<char> & b, unsigned code);
}
