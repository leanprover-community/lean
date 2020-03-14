/*
Copyright (c) 2016-2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Wojciech Nawrocki
*/
#include "util/line_endings.h"
#include <string>
#include <algorithm>

namespace lean {

std::string remove_cr(std::string const & str) {
    std::string ret = str;
    ret.erase(std::remove(ret.begin(), ret.end(), '\r'), ret.end());
    return ret;
}

bool equal_upto_cr(std::string const & a, std::string const & b) {
    return remove_cr(a) == remove_cr(b);
}

}
