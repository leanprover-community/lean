/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <fstream>
#include <iomanip>
#include <list>
#include <string>
#include "kernel/init_module.h"
#include "util/init_module.h"
#include "util/test.h"
#include "util/sstream.h"
#include "util/sexpr/init_module.h"
#include "kernel/quotient/quotient.h"
#include "kernel/inductive/inductive.h"
#include "kernel/standard_kernel.h"
#include "kernel/for_each_fn.h"
#include "checker/text_import.h"
#include "checker/simple_pp.h"

#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#include "shell/emscripten.h"
#endif

using namespace lean;  // NOLINT

struct checker_print_fn {
    std::ostream & m_out;
    environment m_env;
    lowlevel_notations m_notations;
    std::unordered_set<name, name_hash> m_already_printed;

    checker_print_fn(std::ostream & out, environment const & env, lowlevel_notations const & nots) :
        m_out(out), m_env(env), m_notations(nots) {}

    format pp(expr const & e) {
        return simple_pp(m_env, e, m_notations);
    }

    void print_decl(declaration const & d) {
        format fn = compose_many({simple_pp(d.get_name()), space(), format(":"), space(), pp(d.get_type())});

        if (d.is_definition() && !d.is_theorem()) {
            m_out << compose_many({format("def"), space(), fn, space(), format(":="), line(), pp(d.get_value()), line()});
        } else {
            format cmd(d.is_theorem() ? "theorem" : (d.is_axiom() ? "axiom" : "constant"));
            m_out << compose_many({cmd, space(), fn, line()});
        }
    }

    void print_axioms(declaration const & decl) {
        print_axioms(decl.get_type());
        if (decl.is_definition()) print_axioms(decl.get_value());
    }

    void print_axioms(expr const & ex) {
        for_each(ex, [&] (expr const & e, unsigned) {
            if (is_constant(e) && !m_already_printed.count(const_name(e))) {
                auto decl = m_env.get(const_name(e));
                m_already_printed.insert(decl.get_name());
                print_axioms(decl);
                if (decl.is_constant_assumption() && !m_env.is_builtin(decl.get_name()))
                    print_decl(decl);
            }
            return true;
        });
    }

    void handle_cmdline_args(buffer<name> const & ns) {
        for (auto & n : ns) print_axioms(m_env.get(n));
        for (auto & n : ns) print_decl(m_env.get(n));
    }
};

struct dummy_task_queue : public task_queue {
    void wait_for_finish(gtask const &) { throw exception("dummy_task_queue::wait_for_finish"); }
    void fail_and_dispose(gtask const &) {}
    void evacuate() {}
    void join() {}
    void submit(gtask const &) { throw exception("dummy_task_queue::submit"); }
};

int main(int argc, char ** argv) {
#if defined(LEAN_EMSCRIPTEN)
    LEAN_EMSCRIPTEN_ENV
    LEAN_EMSCRIPTEN_FS
#endif

    std::list<std::string> args(argv+1, argv+argc);

    bool verbose = !args.empty() && args.front() == "-v";
    if (verbose) args.pop_front();

    if (args.empty()) {
        std::cout << "usage: leanchecker [-v] export.out [lemma_to_print...]" << std::endl;
        return 1;
    }

    struct initer {
        initer() {
            save_stack_info();
            initialize_util_module();
            initialize_sexpr_module();
            initialize_kernel_module();
            initialize_inductive_module();
            initialize_quotient_module();
        }
        ~initer() {
            finalize_quotient_module();
            finalize_inductive_module();
            finalize_kernel_module();
            finalize_sexpr_module();
            finalize_util_module();
        }
    } initer;

    set_print_fn([] (std::ostream & out, expr const & e) {
        try {
            out << simple_pp(environment(), e, lowlevel_notations());
        } catch (throwable & e) {
            out << "!!!" << e.what() << "!!!";
        }
    });
    if (verbose) std::cerr << std::fixed << std::setprecision(6);

    dummy_task_queue tq;
    set_task_queue(&tq);

    try {
        std::string fn = args.front();
        args.pop_front();
        std::ifstream in(fn);
        if (!in) throw exception(sstream() << "file not found: " << fn);

        unsigned trust_lvl = 0;
        auto env = mk_environment(trust_lvl);
        lowlevel_notations notations;
        import_from_text(in, env, notations, verbose);

        buffer<name> to_print;
        for (auto & arg : args)
            to_print.push_back(string_to_name(arg));

        checker_print_fn(std::cout, env, notations).handle_cmdline_args(to_print);

        unsigned num_decls = 0;
        env.for_each_declaration([&] (declaration const &) { num_decls++; });
        std::cout << "checked " << num_decls << " declarations" << std::endl;

        return 0;
    } catch (throwable & ex) {
        std::cerr << ex.what() << std::endl;
        return 1;
    } catch (std::exception & ex) {
        std::cerr << ex.what() << std::endl;
        return 1;
    }
}
