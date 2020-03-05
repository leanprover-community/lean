/*
Copyright (c) 2016-2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner, Wojciech Nawrocki
*/
#pragma once
#include <string>

namespace lean {
std::string remove_cr(std::string const & str);

bool equal_upto_cr(std::string const & a, std::string const & b);
}
