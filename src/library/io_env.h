
#include "kernel/environment.h"

namespace lean {
environment set_cwd(environment const & env, std::string cwd);
std::string get_cwd(environment const & env);
void initialize_io_env();
void finalize_io_env();
}
