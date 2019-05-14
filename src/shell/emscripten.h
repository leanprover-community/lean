/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Bryan Gin-ge Chen
*/
#define LEAN_EMSCRIPTEN_ENV EM_ASM( \
        var lean_path = process.env['LEAN_PATH']; \
        if (lean_path) { \
            ENV['LEAN_PATH'] = lean_path; \
        } \
        var lean_emscripten_path = process.env['LEAN_EMSCRIPTEN_PATH']; \
        if (lean_emscripten_path) { \
            ENV['LEAN_EMSCRIPTEN_PATH'] = lean_emscripten_path; \
        });
// emscripten cannot mount all of / in the vfs,
// we can only mount subdirectories...
// /home and /tmp are created automatically by emscripten
// see createDefaultDirectories in emscripten's library_fs.js
#define LEAN_EMSCRIPTEN_FS EM_ASM( \
        try { \
            var cwd = process.cwd(); \
            var cwdRoot = '/' + cwd.split('/')[1]; \
            if (cwdRoot !== '/home' && cwdRoot !== '/tmp') FS.mkdir(cwdRoot); \
            FS.mount(NODEFS, { root:cwdRoot }, cwdRoot); \
            FS.chdir(cwd); \
        } catch (e) { \
            console.log(e); \
        });
