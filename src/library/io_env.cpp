
#include "library/io_env.h"
#include "util/path.h"

namespace lean {
struct io_env_ext : public environment_extension {
    std::string m_cwd;
    io_env_ext() : m_cwd(lgetcwd()) { }
};

struct io_env_ext_reg {
    unsigned m_ext_id;
    io_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<io_env_ext>()); }
};

static io_env_ext_reg * g_ext = nullptr;
static io_env_ext const & get_extension(environment const & env) {
    return static_cast<io_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

static environment update(environment const & env, io_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<io_env_ext>(ext));
}

environment set_cwd(environment const & env, std::string cwd) {
    auto ext = get_extension(env);
    ext.m_cwd = cwd;
    return update(env, ext);
}

std::string get_cwd(environment const & env) {
    auto & ext = get_extension(env);
    return ext.m_cwd;
}

void initialize_io_env() {
    g_ext     = new io_env_ext_reg();
}

void finalize_io_env() {
    delete g_ext;
}

}
