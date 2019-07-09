/*
Copyright (c) 2019 James King. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: James King <james@agenultra.com>, Simon Hudon
*/
#include <string>
#include <memory>
#include "library/vm/vm.h"

namespace lean {

    using std::string;

    struct vm_foreign_obj_cell {
        MK_LEAN_RC();
        typedef void * handle_t;
        handle_t m_handle;
        std::string m_filename;
        vm_foreign_obj_cell(handle_t handle, string const & filename)
        : m_rc(0), m_handle(handle),
            m_filename(filename) {};
        ~vm_foreign_obj_cell();
        vm_decl get_cfun(name const & n, unsigned idx, string const & fun_name,
                         buffer<expr> const & _args, expr const & _t);
        void dealloc();
    private:
        vm_foreign_obj_cell(vm_foreign_obj_cell const &);
    };

    class vm_foreign_obj {
    private:
        vm_foreign_obj_cell * m_ptr;
    public:
        vm_foreign_obj():m_ptr(nullptr) {}
        vm_foreign_obj(string const & fname);
        vm_foreign_obj(vm_foreign_obj const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
        vm_foreign_obj(vm_foreign_obj && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
        vm_decl get_cfun(name const & n, unsigned idx, string const & fun_name,
                         buffer<expr> const & _args, expr const & _t) {
            lean_assert(m_ptr); return m_ptr->get_cfun(n, idx, fun_name, _args, _t); }
        vm_foreign_obj & operator=(vm_foreign_obj const & s) { LEAN_COPY_REF(s); }
        vm_foreign_obj & operator=(vm_foreign_obj && s) { LEAN_MOVE_REF(s); }

        ~vm_foreign_obj() { if (m_ptr) { m_ptr->dec_ref(); } }
    };

    class vm_foreign_value : public vm_external {
    private:
        size_t m_size;
        vm_foreign_value(unsigned size) : m_size(size) { }
        virtual void dealloc() override {
            delete [] reinterpret_cast<char *>(this); }
    public:
        static vm_foreign_value * make(size_t size, void * data);
        template <typename T>
        static vm_foreign_value * make(T const & x) { return make(sizeof(T), &x); }
        void * data() { return &m_size + 1; }
        size_t size() const { return m_size; }
        virtual vm_external * ts_clone(vm_clone_fn const &) override {
            return new (new char[ sizeof(vm_foreign_value) + m_size ]) vm_foreign_value(m_size);
        }
        virtual vm_external * clone(vm_clone_fn const &) override {
            return new (get_vm_allocator().allocate(sizeof(vm_foreign_value) + m_size)) vm_foreign_value(m_size);
        }
    };

    void initialize_vm_ffi();

    void finalize_vm_ffi();

}
