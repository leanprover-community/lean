/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include <algorithm>

static void remove_cr(std::string & str) {
    str.erase(std::remove(str.begin(), str.end(), '\r'), str.end());
}

static bool equal_upto_cr(std::string a, std::string b) {
    remove_cr(a);
    remove_cr(b);
    return a == b;
}
