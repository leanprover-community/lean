/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
/**
   \brief Template for simulating "fluid-lets".
   Example:
   {
     flet<int> l(m_field, 1);  // set the value of m_field to 1

   } // restore original value of m_field

*/
template<typename T>
class flet {
    T & m_ref;
    T   m_old_value;
public:
    flet(T & ref, T const & new_value):
        m_ref(ref),
        m_old_value(ref) {
        m_ref = new_value;
    }
    ~flet() {
        m_ref = m_old_value;
    }
};

/**
    \brief Like flet, but without changing the value on scope introduction.

    rlet<T> l(m_field);
    is more or less equivalent to
    flet<T> l(m_field, m_field);
 */
template<typename T>
class rlet {
    T & m_ref;
    T m_old_value;

public:
    rlet(T & ref):
        m_ref(ref),
        m_old_value(ref) {}

    ~rlet() {
        m_ref = m_old_value;
    }
};
}
