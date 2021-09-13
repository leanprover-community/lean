3.33.0c (13 September 2021)
------------------------

Features:
- Allow sorry macro to textualize (#602)
- AST tracking and export (#608)
- Add end-pos support to scanner (#612)
- Log tactic invocations in AST (#614)

Bug fixes:
- Make `injective` semireducible (#604)
- Fix compilation on MacOS 10.14 (#606)
- Fix `elan override` instructions (#605)
- Replace `leanprover` with `leanprover-community` in release build instructions (#610)
- Make `fun_setoid` instance local and not private (#611)
- Rename `int.sub_one_le_of_lt` and `int.lt_of_sub_one_le` (#616)

Changes:
- add `max` / `min` fields to `linear_order` (#609, fixup #615)

3.32.1c (12 August 2021)
------------------------

Changes:
- Remove unification hint `add_succ_defeq_succ_add_hint` (#598)

3.32.0c (10 August 2021)
------------------------

Features:
- Update Windows build instructions (#593)
- `lift_pi_range` (#590)
- Export `self_opt` flag in tlean files (#596)
- Let macros textualize in tleans rather than unfold (#595)

Changes:
- Protect more lemmas (#589)
- Use names `self` and `motive` in recursors (#594)
- Remove uses of `export A (hiding B)` in the core library (#597)
- Remove uses of `reserve notation` (#599)

3.31.0c (29 June 2021)
-----------------------

Features:
- `apply`: produce a better error for missing typeclasses (#577)

Bug fixes:
- Spelling (#573)
- `cases`: fix segfault with equalities of subtypes (#580)
- `cc`: partly disable broken support for symmetric relations (#579)
- Make `trace` thread-safe (#583)
- `simp`: fix segfault with ← and custom relation (#587)

Changes:
- Make `exists.intro` a def again (#582)
- Delete `lazy_list` (#581)

3.30.0c (30 April 2021)
-----------------------

Features:
- Add a brief docstring about unbundled classes (#568)
- Add timing info to verbose output for leanchecker (#567)
- Add docstring for `nat.find` (#566)

Bug fixes:
- Bug with custom recursors on `add_monoid_algebra` (#569)

Changes:
- Avoid well-founded recursion in `nat.mod` and `nat.div` (#570)

3.29.0c (19 April 2021)
-----------------------

Features:
- `leanchecker`: add -v flag to print declaration names (#564)
- `#print` universe parameters of declarations (#558)

Bug fixes:
- Fix let with `coe_sort` (#555)

Changes:
- `acc.rec` should not aggressively reduce proof (#562)
- Use name `self` for argument in structure projections (#561)
- Reduce use of choice (#560)

3.28.0c (15 March 2021)
-----------------------

Features:
- `leanchecker` prints error messages (#548)
- `_root_` can now be used to put declarations in the root namespace (#550)

Bug fixes:
- line wrapping in `to_raw_fmt` (#549)
- The `widget.html.to_string_coe` instance now uses `has_coe_t` (#544)
- Fix in `mt_task_queue` (#552)

Changes:
- `propagate_tags` can now be used interactively (#540)
- Change `fin.sub` to the Lean 4 definition (#541)
- Some lint fixes (#545)
- Update installation instructions (#547)

3.27.0c (25 February 2021)
--------------------------

Features:
 - Export textual .tlean files (#524)
 - Allow `case` to match multiple cases (#508)
 - `specialize` puts goals from underscores first (#530)
 - Make `has_mul.mul` a pattern (#532)
 - Do not clear simp cache unnecessarily (#537)
 - Allow irreducible instances (#538)

Bug fixes:
 - Do not treat empty JSON objects as null (#534)
 - Accidentally quadratic name creation (#535)

Changes:
 - Generalize `exists_unique_of_exists_of_unique` to sort (#526)
 - Sync `ite` and `dite` with lean4 (#531)

3.26.0c (26 January 2021)
-------------------------

Bug fixes:
  - Fix addressing bug in pretty printer (#520)

3.25.0c (21 January 2021)
-------------------------

Features:
  - `try_for_time` interruption function (#517)
  - Add primitives for GPT integration (#510)
  - Record simplification lemmas and export them to `tactic.simplify` (#497)

Bug fixes:
  - Correct minor typo in docstring (#518)

3.24.0c (4 January 2021)
-------------------------

Features:
- Position argument with `insert_text` (#501)
- Check that classes are types (#502)
- Enable type class cache in nested resolution problems (#505)

Bug fixes:
- Tests on arm64 (#498)
- Make `infer_instance` work on sorts (#506)
- Fix universe levels in punit lemmas (#507)
- Ensure `json.parse`/`json.unparse` are inverses (#509)

Changes:
- Improve default termination measure for mutually recursive functions (#496)
- Make `is_lawful_singleton` a Prop (#499)
- `well_founded.recursion` is a definition now (#503)

3.23.0c (29 October 2020)
-------------------------

Features:
- Expose `kabstract` in `type_context` to the VM (#391)
- Add position information to declarations added in user commands (#488)

Bug fixes:
- The `a` bug is replaced by the `ᾰ` bug (#490)

Changes:
- New instance naming heuristic (#458, #493)
- `by_contradiction` uses classical logic and the name `h` (#491)

3.22.0c (27 October 2020)
-------------------------

Features:
- Improve error handling of `for` and `find` in `conv` mode (#482, #485)

Bug fixes:
- Fix typos in docstrings for `tactic.focus` and `tactic.focus'` (#483)

Changes:
- Remove `lean --doc` (which never actually did anything) (#480)
- Add `decidable_*` assumptions to `linear_order` and remove `decidable_linear_order` (#484)

3.21.0c (12 October 2020)
-------------------------

Features:
- Simplify definition of `band` and `bor` (#466)
- More advice in docstrings for `Exists`, `not`, `and`, and `or` (#296)

Bug fixes:
- Fix typo in docstring for `tactic.exact` (#472)
- Fix missing code block in [widget server docs](widget_server.md) (#473)

Changes:
- Remove global notation for `vector.cons` (#471)

3.20.0c (9 September 2020)
--------------------------

Features:
- Options are refreshed when the simplifier is entered. (#456)
- JSON support for widgets (#453)
- More definition and theorem docstrings (#463)

Bug fixes:
- Typeclass args for `monad_state_trans` were flipped. (#461)
- `resolve_constant` now handles `parameters` correctly. (#462)

Changes:
- Remove `nat.pow` from the core library (#457)

3.19.0c (27 August 2020)
------------------------

Features:
- There is a new option `extends_priority` which controls the priority of instances produced by `extends`. It is set to 100 by default. (#440)
- Add [docs for the Lean server API](widget_server.md) (#443)

Bug fixes:
- Fix name generation by `injection_with` (#430)
- Fix bug in `in_current_file` (#432)
- Fix docstring in `introv` (#434)
- Fix parse precedence for `#html` (#444)
- Add `\fl` and `\fr` to `lstlean.tex` (#448)

Changes:
- Avoid `classical.choice` in `lt_of_le_of_ne` (#428)
- Remove usage of the axiom of choice from basic `nat` and `int` lemmas, remove `private` from internal lemmas about `int` and move the `decidable.*` order theorems from mathlib (#446)
- Change syntax of `guard_hyp` from `guard_hyp h := t` to `guard_hyp h : t` and support `guard_hyp h : t := val` for checking `let` bindings (#445, #449)
- Make `fin` a subtype (#452)

3.18.4c (30 July 2020)
----------------------

Features:
- Ensure `@max (order_dual α) = @min α` (#425)

Bug fixes:
- Description for `small_nat` (#424)
- More set replacement fixes (#426, fixes #422 and #423)

3.18.3c (29 July 2020)
----------------------

Features:
- Show VM overrides in info request (#417)

Bug fixes:
- Support `{(1 : α)}` and `{(∘), (∘)}` (#420, fixes #419 and #418)

3.18.2c (28 July 2020)
----------------------

Bug fixes:
- Fix `{(0,1)}` (#415)

3.18.1c (28 July 2020)
----------------------

Bug fixes:
- Update local instances (#412, fixes #411)

3.18.0c (28 July 2020)
----------------------

Features:
- Notation for set replacement (#402)

Bug fixes:
- Drop non-local-constant exprs from `cases` output (#390)
- Freeze local instances for definition parameters (#403, fixes #397)
- Freeze local instances in `#check` (#404, fixes #398)
- Honor `as_is` attribute for functions (#399)
- Fix VM environment issue (#405)
- Remove `tactic.norm_num` (#406)
- Fix injection introducing too many hyps (#407, fixes #400)
- Handle corner cases in `by_cases` (#409)

Changes:
- Use a structure for `well_founded` (#408)

3.17.1c (8 July 2020)
---------------------

Features:
- Reuse type-class cache (#383)

Bug fixes:
- Info error for commands directly after imports (#386, fixes #382)

3.17.0c (6 July 2020)
---------------------

Features:
- Refactor widgets to use hooks (#363, #369)
- `component.with_effects` (#370)
- Add "copy text" effect. (#375)

Bug fixes:
- Add margin to local const names in tactic state (#365)
- Prevent segfault in `apply` (#373, fixes #372)
- Fix address incorrect issue in `pp_tagged` (#371)
- Abort if no input consumed in `module_parser` (#377, fixes #374)
- Do not unify `(1 : ℕ)` with `(1 : ℤ)` (#376, fixes #362)

Changes:
- Fix vacuous assumptions in nat lemmas (#366)
- Remove `has_neg` instance for `set` (#367)
- Mark `dif_ctx_congr` as `@[congr]` (#378)

Server protocol changes:
- The response of the `widget_event` request may now contain effects.

3.16.5c (25 June 2020)
----------------------

Features:
- Add comment-like string blocks (#352)
- Add widgets to trace messages (#355)
- Show case tags in goal widget (#357)

Bug fixes:
- Handle exceptions in `ts_clone` (#350)
- Support `sorry #` (#356)

Server protocol changes:
- The (Lean error) messages returned by the server may now contain an additional `"widget"` field.

3.16.4c (22 June 2020)
----------------------

Features:
- Use `tactic_state_context_cache` more (#347)
- Goal widget: collect locals with the same type and local filtering (#346)

Bug fixes:
- Fix error message in `cases`

3.16.3c (18 June 2020)
----------------------

Bug fixes:
- Remove as-is annotations (#338, fixes #334)
- Handle EOF in `skip_to_pos` (#342, fixes #85)
- Fix holes with space in name (#343)

Features:
- Add profiling for user attributes (#328)
- Profile user commands (#329)
- Support `lean --profile --run` (#337)
- Add `parser.{any_char,digit,nat}` (#331)
- Cache type-class searches w/o mvars (#332)

Changes:
- Put `is_strict_total_order` in `Prop` (#327)
- Remove redundant lemmas (#321)

3.16.2c (12 June 2020)
----------------------

Bug fixes:
- Stop scanning after `#exit` (#318, fixes #309)
- Allow `variables (A B : Type*)` (#319, fixes #29)
- Escape names using French quotes by default (#320, fixes #114)
- Fix `lean --deps` (#323)
- Selection disco issue in tactic state widget (#324)

Features:
- Add `get_widget` server request (#314)
- Allow namespaces inside sections (#317, fixes #315)

Server protocol changes:
- The `info` request no longer returns the widget HTML.  Instead it returns an `id` field in addition to `line` and `column`.  The `get_widget` request now returns the HTML.  The `widget_event` request also requires an `id` argument.

3.16.1c (10 June 2020)
----------------------

Bug fixes:
- Add key to `li` in `tactic_view_component` (#311)
- Fix widget updates in `by ...` (#312)

3.16.0c (10 June 2020)
----------------------

Features:
- Add docstrings for `cc_state` primitives (#295)
- Use `BUILD_TESTING` to enable or disable building tests (#292)
- Additional meta constants (#294)
- Add `@[pp_nodot]` (#297)
- Make widget look more like current tactic state (#303)
- Show term-proof goals as widgets (#304, #306)
- Add holes for underscores (#307)

Bug fixes:
- Fix case of header files for building on case-sensitive filesystems (#290)
- Remove useless setting of `_GLIBCXX_USE_CXX11_ABI` with MinGW (#293)
- Fix guards to make it possible to build for BSD systems (#291)
- Rename `tactic.tactic.run_simple` -> `tactic.run_simple` (#298)
- Use instance instead of semireducible transparency in type-class synthesis (#300)
- Widget events contain position (#301)
- Server: do not cancel info queries, etc. (#308)

Changes:
- Lower precedence of unary `-` (#287)

3.15.0c (28 May 2020)
---------------------

Features:
  - Support for structured formatting using `eformat` (#276)
  - Show goals for subterms (#275, #277)
  - Freeze instances in the simplifier (#273)
  - Support local attribute with docstring (#271)
  - VM objects may be hashed (#262)
  - `expr.coord` and `expr.address` (#260)
  - Add `list.map_with_index` to core library (#259)
  - Add `expr.instantiate_vars_core` (#261)
  - Don't check levels on meta inductives (#263)

Bug fixes:
  - Preserve VM code indexes across instances (#283)
  - Fixes a VM environment cache not updating (#280)
  - Do not use fseek in io.fs.read (#278)
  - Dot-notation pretty-printing (#269)

Changes:
  - Elaborate structure instances left-to-right (#282)
  - Remove duplicated namespaces (#267)
  - Remove `(|` and `|)` aliases (#265)

### Special feature: widgets

#### Lean API
- Add widgets. This is an HTML-based UI framework for generating html within lean to enable interactive UI
  in the infoview in vscode and on the web.
- Add `tactic.save_widget: pos → widget.component tactic_state string → tactic unit`. Examples of widgets can be found in `library/widget/examples.lean`.
  Widgets are registered in exactly the same way as `save_info_thunk` saves text.
- Use the `#html` command to view `html empty` or `component tactic_state string` widgets.
- Add a 'structured format' pretty printing system `tactic_state.pp_tagged : tactic_state → expr → eformat`.
  `eformat := tagged_format (expr.address × expr)`.
  `tagged_format α : Type` performs the same role as `format` except that there is a special constructor
  `tag : α → tagged_format → tagged_format` that contains information about
  which subexpression caused this string to be rendered.
  This is used to implement a widget which allows the user to hover over a pretty printed string
  and view information about the subexpressions that build up the original expression.
  For example, this lets you view types of pretty printed expressions and view implicit arguments.
- Add numerous docstrings

#### Frontend/library changes

- Overhaul pretty printer so that it can
  provide information about expression addresses.
  This required making it templated to output `T` instead of `format`.
  Currently `T` may be instantiated with `lean::format` or `lean::eformat`.
  See `src/library/vm/vm_eformat` and
- Info manager now supports widgets.
- Server `info` response may now include a `"widget"` field on the returned `"record"` json.
- Server has a new command `widget_event` to enable interactive widgets
- The main code for widgets can be found in `src/frontends/widget.(h|cpp)`.
- VM objects can now be hashed, with the exception of some `vm_external`s which hash to zero.
  This is needed to verify the identity of components in the widget reconciliation engine.
- server has an option `-no-widgets` or `-W` for turning off widget reporting. This is used in the interactive tests.

v3.14.0c (20 May 2020)
----------------------

Features:
 - Coercions also trigger if the types have metavariables (#251)
 - Better error message on missing imports (#253)
 - Add `add_eqn_lemma` function (#254)

v3.13.2c (18 May 2020)
----------------------

Fixes:
 - Fix `olean_doc_strings` (#249)

v3.13.1c (17 May 2020)
----------------------

Fixes:
 - Protect and rename some `nat` and `int` lemmas that are superseded in mathlib (#229)

v3.13.0c (16 May 2020)
----------------------

Features:
 - use persistent data structures, to improve performance
   of (module) docstrings (#241)
 - cache constructed `simp_lemma` objects (#234)
 - support `local attribute [-instance]` (#240)
 - show goal after `;` (#239)
 - `==`: compare id (#238)
 - mark deps of fixed as fixed (#237)


Changes:
 - Most of `library/init/algebra/*` has been deleted,
   as part of moving the algebraic hierarchy to mathlib (#229)

v3.12.0c (14 May 2020)
----------------------

Features:
  - Tactic combinators with informative results (#212)
  - `has_singleton` is a new typeclass (#217)
  - Add instances for `has_repr name`, `has_repr case_tag`, and `has_to_format case_tag` (#230)

Changes:
  - `library/init/function`: use dot notation, add some docstrings (#216)
  - `tactic.all_goals` is now called `tactic.all_goals'`, etc. (#212)
  - `norm_num` is removed (#224)
  - Parse `{a,b,c}` as right associative (#153)
  - Refactor case tags (#228)
  - Enable `pp.generalized_field_notation` by default (#227)

v3.11.0c (8 May 2020)
---------------------

Feature:
  - Do not unfold irreducible definitions in unification (#211)
  - Instantiate metavariables in `rw` (#213)

Bug fixes:
  - Fix docstring of tactic.interactive.rename (#210)

v3.10.0c (2 May 2020)
---------------------

Features:
  - `by calc ...` is now equivalent to `by refine calc ...` (#203)
  - Flag to use out-of-date oleans (#208)
  - Order notation by priority in pretty-printer (#207)
  - Improve congruence lemmas for `coe_fn` (#209)
  - Port `rename` tactic from mathlib (#205)

Bug fixes:
  - `simp [← foo]` avoids looping if `foo` is already in the simp set (#198)

Changes:
  - `init.category` has been renamed to `init.control` (#202)
  - `string.has_decidable_eq` is now implemented by foot (#204)

v3.9.0c (19 April 2020)
----------------------

Features:
  - The VM supports string literals (#185, #187)
  - Imports are parsed in an indentation-sensitive way. Compare:
    ```lean
    import foo
      bar
    open_locale classical -- runs user command
    ```
    and
    ```lean
    import foo
      bar
      open_locale classical -- imports open_locale and classical modules
    ```
    This makes it easier to run user commands at the start of files. (#188)
  - The parser now has access to the local scope and can parse expressions as patterns (#192)
  - `mmap` and `map` functions for `d_array`, `array`, and `buffer` (#190)

Bug fixes:
  - The order of emetas has been reversed in `simp_lemmas` (#183)
  - Universe parameters are collected from anonymous instances (#189)
  - Nested comment parsing in doc strings was fixed (#191)

Changes:
  - The performance of `array.map` has been greatly improved (#186)
  - A frequently-violated assertion was removed from the elaborator (#194)

v3.8.0c (9 April 2020)
----------------------

Features:
  - The VM implementation of functions can be overriden (#48)
  - More and better doc strings for the core library (#166)

Bug fixes:
  - `simp` instantiates the metavariables in the goal before simplifying (#170)
  - `app_builder` is more robust (#165)
  - Assertion violation in `simp_inductive` (#173)

Changes:
  - `expr.subst` constructs an application if the left expression is not a lambda (#180)
  - `if_simp_congr` is removed, simp now produces the correct decidability instance when simplifying if-then-else (#159)
  - `float.{ceil,floor,trunc,round}` now return integers (#176)
  - `default` is now an export (#161)
  - `prod.map` and `function.uncurry` don't use pattern matching (#161)
  - The type argument in `has_zero.zero` and `has_one.one` is implicit (#169)
  - Inductives/structures/structure fields now default to implicit arguments (#175)
  - `add_lt_add_left` and `mul_le_mul*` fields are removed (#167)
  - `ordered_comm_group` is renamed to `ordered_add_comm_group` (#174)

v3.7.2c (20 Mar 2020)
---------------------

Bug fix:
  - Open .oleans in binary mode on Windows (#155)

v3.7.1c (16 Mar 2020)
---------------------

Bug fix:
  - Allow loading standalone .olean files (#150)

v3.7.0c (13 Mar 2020)
---------------------

Features:
  - `simp` can rewrite subsingletons (#134)
  - Files are recompiled based on hash code instead of timestamp (#140)
  - `mk_protected`, `add_protected`, `is_protected` functions (#138)
  - `has_attribute` and `copy_attribute` now expliclity support non-persistent attributes (#66)

Bug fixes:
  - Fix the implementation of the instance `has_coe (tactic α) (parser α)` (#136 and #147)
  - `simp` catches exception (e.g. from type class resolution, #142)
  - `(+) = (λ x y, x + y)` unifies now (#141)

Changes:
  - `apply` solves instances in forward order (#67)
  - Type class resolution solves instance arguments from right-to-left (#139)
  - Type class resolution skips assigned metavariables (#135)
  - Signature of `has_attribute` and `copy_attribute` has changed (#66)

v3.6.1c (2 Mar 2020)
--------------------

Bug fix:
  - Correctly reference the community fork of Lean in `leanpkg.toml` (#131)

v3.6.0c (26 Feb 2020)
---------------------

Features:
 - Remove `discrete_field` (#119)
 - Remove simp attribute from `sub_eq_add_neg` (#117)
 - Replace `insert` definition by export (#115)
 - Remove simp attribute from `add_comm` and `add_left_comm` (#65)
 - simp with reversed lemmas: `simp ← foo` (#100)
 - Allow nested block comments in docstrings (#113)

Bug fixes:
 - Include mathlib fixes to `wf_tacs` (#121)
 - Typos in docstrings (#125)

Changes:
 - `discrete_field` is now just `field` (#119)
 - `add_comm`, `add_left_comm`, and `sub_eq_add_neg` are no longer simp lemmas
 - `insert` is no longer a definition
 - Nested block comments are now allowed in docstrings

v3.5.1c (4 Feb 2020)
--------------------

Features:
- Allow `change` to be used to rename bound variables (#96)
- Annotate pretty-printed output with full constant names (#89)
- Import modules from meta code (#88)
- Make `add_interactive` copy the doc string (#97)
- Avoid version warning for external Leans in leanpkg (#106)

Bugfixes:
- Force tactic type in `run_cmd` (#103)
- `?m_1` and `(λ x, ?m_1) y` should be definitionally equal (#107)

v3.5.0c (26 Dec 2019)
--------------

This is the first community release of Lean 3.

*Features*

 * Add `native.float` for using floating point values within meta functions.

 * Add `reflect (p : parser α) [r : reflectable p] : parser expr` def for parsing raw `expr`s. (#33)

 * Add `tactic.unsafe.type_context` and `local_context` for directly interacting with Lean's type context.

   This means that metavariables and local constants can be directly declared and assigned. (#69)

 * Docstrings are now supported on inductive constructors. (#61)

 * Add `environment.add_defn_eqns` to programmatically create a definition that uses the equation compiler. (#26)

 * Add `environment.add_ginductive` to give tactics access to the utility lemmas associated with inductive type declaration. (#3)

 * Improve file API. Add support for UNIX sockets. (#20, #31)

 * Add `lean.parser.itactic`, a tactic block parser. (#19)

 * Add `interactive.executor`, a class to implement custom tactic monads in `begin ... end` blocks. (#10)

 * Add `expr` serialization/deserialization functions. (#6)

 * Improve and add numerous docstrings.

 * Module documentation is now stored in .olean files to allow documentation to be automatically generated. (#54)

 * Documentation of all imported modules is now exposed via the `olean_doc_strings` tactic. (#81)

*Bug Fixes*

 * build: fix emscripten build in travis (#68)
 * CMakeLists.txt: GCC 9.1.0 miscompiles certain if statements #63
 * tactic/revert_tactic: disallow duplicates (#56)
 * level: give level.instantiate correct type (#46)
 * documentation: The closing code fence must match opening fence. (#40)
 * emscripten: fix FS issue: don't mkdir in docker (#39)
 * emscripten: fix emscripten build (#17)
 * tactic/case: `case` fails when used with `let` (#32)
 * tactic/revert_lst: check that the provided expressions are variables (#12)
 * tactic/type_check: do not assign to meta variables (#86)
 * init/algebra/field: repeated instance (#8)
 * Add an additional check to `type_context_old::mk_class_instance_at(lctx,type)` to fix issue #55. (#79)

*Changes*

 * Notation removed: `=<<`, `>=>`, `<=<`
 * `transfer` and `relator` namespaces removed.

v3.4.2 (18 Jan 2019)
-------------

Patch release

*Features*

* `leanpkg`: Allow specifying a branch to use for `leanpkg upgrade` ([#1981](https://github.com/leanprover/lean/pull/1981))

*Changes*

* Fix the definition of `list.lt`

* Make `leanpkg` work when installed in a path containing spaces

* `io`: Encode/decode UTF-8 for text-mode streams

* Remove `coinductive` predicates and `transfer`. To be moved to [mathlib](https://github.com/leanprover/mathlib) instead.

* Windows: Ignore file changes that only changed line endings

v3.4.1 (28 April 2018)
-------------

Bugfix release: Fix a regression concerning type ascriptions in function position

v3.4.0 (16 April 2018)
-------------

*Features*

* Implement [RFC #1820](https://github.com/leanprover/lean/issues/1820)

* Add `string.iterator` abstraction for traversing strings.
  The VM contains an efficient implementation of this type.

* Add support for non-ASCII char literals. Example: `'α'`.

* Unicode escape characters in string and char literals. For example, `'\u03B1'` is equivalent to `'α'`.

* Predictable runtime cost model for recursive functions. The equation compiler uses
  different techniques for converting recursive equations into recursors and/or
  well-founded fixed points. The new approach used in the code generator ignores
  these encoding tricks when producing byte code. So, the runtime cost model
  is identical to the one in regular strict functional languages.

* Add `d_array n α` (array type where value type may depend on index),
  where (α : fin n → Type u).

* Add instance for `decidable_eq (d_array n α)` and `decidable_eq (array n α)`.
  The new instance is more efficient than the one in mathlib because it doesn't
  convert the array into a list.

* Add aliasing pattern syntax `id@pat`, which introduces the name `id` for the value matched by
  the pattern `pat`.

* Add alternative syntax `{..., ..s}` for the structure update `{s with ...}`.
  Multiple fallback sources can be given: `{..., ..s, ..t}` will fall back to
  searching a field in `s`, then in `t`. The last component can also be `..`,
  which will replace any missing fields with a placeholder.
  The old notation will be removed in the future.

* Add support for structure instance notation `{...}` in patterns. Use `..` to ignore
  unmatched fields.

* Type class `has_equiv` for `≈` notation.

* Add `funext ids*` tactic for applying the funext lemma.

* Add `iterate n { t }` for applying tactic `t` `n` times.
  Remark: `iterate { t }` applies `t` until it fails.

* Add `with_cases { t }`. This tactic applies `t` to the main goal,
  and reverts any new hypothesis in the resulting subgoals. `with_cases` also enable "goal tagging".
  Remark: `induction` and `cases` tag goals using constructor names. `apply` and `constructor` tag goals
  using parameter names. The `case` tactic can select goals using tags.

* Add `cases_matching p` tactic for applying the `cases` tactic to a hypothesis `h : t` s.t.
  `t` matches the pattern `p`. Alternative versions: `cases_matching* p` and `cases_matching [p_1, ..., p_n]`.
  Example: `cases_matching* [_ ∨ _, _ ∧ _]` destructs all conjunctions and disjunctions in the main goal.

* Add `cases_type I` tactic for applying the `cases` tactic to a hypothesis `h : I ...`.
  `cases_type! I` only succeeds when the number of resulting goals is <= 1.
  Alternative versions: `cases_type I_1 ... I_n`, `cases_type* I`, `cases_type!* I`.
  Example: `cases_type* and or` destructs all conjunctions and disjunctions in the main goal.

* Add `constructor_matching p` tactic. It is syntax sugar for `match_target p; constructor`.
  The variant `constructor_matching* p` is more efficient than `focus1 { repeat { match_target p; constructor } }`
  because the patterns are compiled only once.

* `injection h` now supports nested and mutually recursive datatypes.

* Display number of goals in the `*Lean Goal*` buffer (if number of goals > 1).

* `hide id*` command for hiding aliases.
  The following command  hides the alias `is_true` for `decidable.is_true`.
  ```
  hide is_true
  ```

* Add `abbreviation` declaration command. `abbreviation d : t := v` is equivalent to
  `@[reducible, inline] def d : t := v` and a kernel reducibility hint.
  Before this command, we had to use meta programming for setting the kernel reducibility hint.
  This was problematic because we could only define abbreviations after the meta programming
  framework was defined.

* Add "smart unfolding". The idea is to prevent internal compilation details
  used by the equation compiler to "leak" during unification, tactic execution and
  reduction. With "smart unfolding", the term `nat.add a (nat.succ b)` reduces
  to `nat.succ (nat.add a b)` instead of `nat.succ (... incomprehensible mess ...)`.
  This feature addresses a problem reported by many users.
  See [issue #1794](https://github.com/leanprover/lean/issues/1794).
  The command `set_option type_context.smart_unfolding false` disables this feature.

* Add support for "auto params" at `simp` tactic. Example: given
  ```
  @[simp] lemma fprop1 (x : nat) (h : x > 0 . tactic.assumption) : f x = x := ...
  ```
  The simplifier will try to use tactic `assumption` to synthesize parameter `h`.

* Add interactive `sorry` tactic (alias for `admit`).

* `simp` now reduces equalities `c_1 ... = c_2 ...` to `false` if `c_1` and `c_2` are distinct
   constructors. This feature can be disabled using `simp {constructor_eq := ff}`.

* `simp` now reduces equalities `c a_1 ... a_n = c b_1 ... b_n` to `a_1 = b_1 /\ ... /\ a_n = b_n` if `c` is a constructor.
   This feature can be disabled using `simp {constructor_eq := ff}`.

* `subst` and `subst_vars` now support heterogeneous equalities that are actually homogeneous
   (i.e., `@heq α a β b` where `α` and `β` are definitionally equal).

* Add interactive `subst_vars` tactic.

* Add `leanpkg add foo/bar` as a shorthand for `leanpkg add https://github.com/foo/bar`.

* Add `leanpkg help <command>`.

* Add `[norm]` simp set. It contains all lemmas tagged with `[simp]` plus any
  lemma tagged with `[norm]`.
  These rules are used to produce normal forms and/or reduce the
  number of constants used in a goal. For example, we plan to
  add the lemma `f <$> x = x >>= pure ∘ f` to `[norm]`.

* Add `iota_eqn : bool` field to `simp_config`. `simp {iota_eqn := tt}` uses
  all non trivial equation lemmas generated by equation/pattern-matching compiler.
  A lemma is considered non trivial if it is not of the form `forall x_1 ... x_n, f x_1 ... x_n = t` and
  a proof by reflexivity. `simp!` is a shorthand for `simp {iota_eqn := tt}`.
  For example, given the goal `... |- [1,2].map nat.succ = t`, `simp!` reduces the left-hand-side
  of the equation to `[nat.succ 1, nat.succ 2]`. In this example, `simp!` is equivalent to
  `simp [list.map]`.

* Allow the Script, Double-struck, and Fractur symbols from
  Mathematical Alphanumeric Symbols: https://unicode.org/charts/PDF/U1D400.pdf
  to be used as variables Example: `variables 𝓞 : Prop`.

* Structure instance notation now allows explicitly setting implicit structure fields

* Structure instance notation now falls back to type inference for inferring the
  value of a superclass. This change eliminates the need for most `..` source specifiers
  in instance declarations.

* The `--profile` flag will now print cumulative profiling times at the end of execution

* do notation now uses the top-level, overloadable `bind` function instead of `has_bind.bind`,
  allowing binds with different type signatures

* Structures fields can now be defined with an implicitness infer annotation and parameters.
  ```
  class has_pure (f : Type u → Type v) :=
  -- make f implicit
  (pure {} {α : Type u} : α → f α)
  ```

* Add `except_t` and `reader_t` monad transformers

* Add `monad_{except,reader,state}` classes for accessing effects anywhere in a monad stack
  without the need for explicit lifting. Add analogous `monad_{except,reader,state}_adapter`
  classes for translating a monad stack into another one with the same shape but different
  parameter types.

*Changes*

* Command `variable [io.interface]` is not needed anymore to use the `io` monad.
  It is also easier to add new io primitives.

* Replace `inout` modifier in type class declarations with `out_param` modifier.
  Reason: counterintuitive behavior in the type class resolution procedure.
  The result could depend on partial information available in the `inout`
  parameter. Now a parameter `(R : inout α → β → Prop)` should be written
  as `(R : out_param (α → β → Prop))` or `(R : out_param $ α → β → Prop)`.
  Remark: users may define their own notation for declaring `out_param`s.
  Example:
  ```
  notation `out`:1024 a:0 := out_param a
  ```
  We did not include this notation in core lib because `out` is frequently used to
  name parameters, local variables, etc.

* `case` tactic now supports the `with_cases { t }` tactic. See entry above about `with_cases`.
  The tag and new hypotheses are now separated with `:`. Example:
  - `case pos { t }`: execute tactic `t` to goal tagged `pos`
  - `case pos neg { t }`: execute tactic `t` to goal tagged `pos neg`
  - `case : x y { t }`: execute tactic `t` to main goal after renaming the first two hypotheses produced by preceding `with_case { t' }`.
  - `case pos neg : x y { t }` : execute tactic `t` to goal tagged `pos neg` after renaming the first two hypotheses produced by preceding `with_case { t' }`.

* `cases h` now also tries to clear `h` when performing dependent elimination.

* `repeat { t }` behavior changed. Now, it applies `t` to each goal. If the application succeeds,
  the tactic is applied recursively to all the generated subgoals until it eventually fails.
  The recursion stops in a subgoal when the tactic has failed to make progress.
  The previous `repeat` tactic was renamed to `iterate`.

* The automatically generated recursor `C.rec` for an inductive datatype
  now uses `ih` to name induction hypotheses instead of `ih_1` if there is only one.
  If there is more than one induction hypotheses, the name is generated by concatenating `ih_`
  before the constructor field name. For example, for the constructor
  ```
  | node (left right : tree) (val : A) : tree
  ```
  The induction hypotheses are now named: `ih_left` and `ih_right`.
  This change only affects tactical proofs where explicit names are not provided
  to `induction` and `cases` tactics.

* `induction h` and `cases h` tactic use a new approach for naming new hypotheses.
   If names are not provided by the user, these tactics will create a "base" name
   by concatenating the input hypothesis name with the constructor field name.
   If there is only one field, the tactic simply reuses the hypothesis name.
   The final name is generated by making sure the "base" name is unique.
   Remarks:
   - If `h` is not a hypothesis, then no concatenation is performed.
   - The old behavior can be obtained by using the following command
   ```
   set_option tactic.induction.concat_names false
   ```
   This change was suggested by Tahina Ramananandro. The idea is to have more
   robust tactic scripts when helper tactics that destruct many hypotheses automatically
   are used.
   Remark: The new `guard_names { t }` tactical can be used to generate
   robust tactic scripts that are not sensitive to naming generation strategies used by `t`.

* Remove `[simp]` attribute from lemmas `or.assoc`, `or.comm`, `or.left_comm`, `and.assoc`, `and.comm`, `and.left_comm`, `add_assoc`, `add_comm`, `add_left_com`, `mul_assoc`, `mul_comm` and `mul_left_comm`.
  These lemmas were being used to "sort" arguments of AC operators: and, or, (+) and (*).
  This was producing unstable proofs. The old behavior can be retrieved by using the commands `local attribute [simp] ...` or `attribute [simp] ...` in the affected files.

* `string` is now a list of unicode scalar values. Moreover, in the VM,
  strings are implemented as an UTF-8 encoded array of bytes.

* `array α n` is now written `array n α`. Motivation: consistency `d_array n α`.

* Move `rb_map` and `rb_tree` to the `native` namespace. We will later add
  pure Lean implementations. Use `open native` to port files.

* `apply t` behavior changed when type of `t` is of the form `forall (a_1 : A_1) ... (a_n : A_n), ?m ...`, where `?m` is an unassigned metavariable.
  In this case, `apply t` behaves as `apply t _ ... _` where `n` `_` have been added, independently of the goal target type.
  The new behavior is useful when using `apply` with eliminator-like definitions.

* `ginduction t with h h1 h2` is now `induction h : t with h1 h2`.

* `apply_core` now also returns the parameter name associated with new metavariables.

* `apply` now also returns the new metavariables (and the parameter name associated with them). Even the assigned metavariables are returned.

* `by_cases p with h` ==> `by_cases h : p`

* leanpkg now always stores .lean package files in a separate `src` directory.

* Structure constructor parameters representing superclasses are now marked as instance implicit.
  Note: Instances using the {...} structure notation should not be affected by this change.

* The monad laws have been separated into new type classes `is_lawful_{functor,applicative,monad}`.

* `unit` is now an abbreviation of `punit.{0}`

*API name changes*

* `monad.has_monad_lift(_t)` ~> `has_monad_lift(_t)`
* `monad.map_comp` ~> `comp_map`
* `state(_t).{read,write}` ~> `{get,put}` (general operations defined on any `monad_state`)
* deleted `monad.monad_transformer`
* deleted `monad.lift{n}`. Use `f <$> a1 <*> ... <*> an` instead of `monad.lift{n} f a1 ... an`.
* merged `has_map` into `functor`
* `unit_eq(_unit)` ~> `punit_eq(_punit)`

v3.3.0 (14 September 2017)
-------------

*Features*

* In addition to user-defined notation parsers introduced in Lean 3.2.0, users may now also define top-level commands in Lean. For an example, see the [`coinductive` command](https://github.com/leanprover/lean/blob/814a5edaf172c3835c000e3f631bddd85bd879ab/library/init/meta/coinductive_predicates.lean#L551-L552) that has been ported to the new model.

* Add new simplifier configuration option `simp_config.single_pass`. It is useful for simplification rules that may produce non-termination.
  Example: `simp {single_pass := tt}`

* The rewrite tactic has support for equational lemmas. Example: Given a definition `f`, `rw [f]` will try to rewrite the goal using the equational lemmas for `f`.
  The tactic fails if none of the equational lemmas can be used.

* Add `simp * at *` variant. It acts on all (non dependent propositional) hypotheses.
  Simplified hypotheses are automatically inserted into the simplification set
  as additional simplification rules.

* Add `«id»` notation that can be used to declare and refer to identifiers containing prohibited characters.
  For example, `a.«b.c»` is a two-part identifier with parts `a` and `b.c`.

* `simp` tactic now handles lemmas with metavariables. Example `simp [add_comm _ b]`.

* `conv { ... }` tactic for applying simplification and rewriting steps.
  In the block `{...}`, we can use tactics from `conv.interactive`.
  Examples:
  - `conv at h in (f _ _) { simp }` applies `simp` to first subterm matching `f _ _` at hypothesis `h`.
  - `conv in (_ = _) { to_lhs, whnf }` replace the left-hand-side of the equality in target with its weak-head-normal-form.
  - `conv at h in (0 + _) { rw [zero_add] }`
  - `conv { for (f _ _) [1, 3] {rw [h]}, simp }`, first execute `rw[h]` to the first and third occurrences of an `f`-application,
     and then execute `simp`.

* `simp` tactics in interactive mode have a new configuration parameter (`discharger : tactic unit`)
   a tactic for discharging subgoals created by the simplifier. If the tactic fails, the simplifier
   tries to discharge the subgoal by reducing it to `true`.
   Example: `simp {discharger := assumption}`.

* `simp` and `dsimp` can be used to unfold projection applications when the argument is a type class instance.
   Example: `simp [has_add.add]` will replace `@has_add.add nat nat.has_add a b` with `nat.add a b`

* `dsimp` has several new configuration options to control reduction (e.g., `iota`, `beta`, `zeta`, ...).

* Non-exhaustive pattern matches now show missing cases.

* `induction e` now also works on non-variable `e`. Unlike `ginduction`, it will not introduce equalities relating `e` to the inductive cases.

* Add notation `#[a, b, c, d]` for `bin_tree.node (bin_tree.node (bin_tree.leaf a) (bin_tree.leaf b)) (bin_tree.node (bin_tree.leaf c) (bin_tree.leaf d))`.
  There is a coercion from `bin_tree` to `list`. The new notation allows to input long sequences efficiently.
  It also prevents system stack overflows.

* Tactics that accept a location parameter, like `rw thm at h`, may now use `⊢` or the ASCII version `|-`
  to select the goal as well as any hypotheses, for example `rw thm at h1 h2 ⊢`.

* Add `user_attribute.after_set/before_unset` handlers that can be used for validation as well as side-effecting attributes.

* Field notation can now be used to make recursive calls.

```
def list.append : list α → list α → list α
| []       l := l
| (h :: s) t := h :: s.append t
```

* leanpkg now stores the intended Lean version in the `leanpkg.toml` file and reports a warning if the version does not match the installed Lean version.

* `simp` and `dsimp` can now unfold let-bindings in the local context.  Use `dsimp [x]` or `simp [x]` to unfold the let-binding `x : nat := 3`.

* User-defined attributes can now take parameters parsed by a `lean.parser`. A `[derive]` attribute that can derive typeclasses such as `decidable_eq` and `inhabited` has been implemented on top of this.

*Changes*

* We now have two type classes for converting to string: `has_to_string` and `has_repr`.
The `has_to_string` type class in v3.2.0 is roughly equivalent to `has_repr`.
For more details, see discussion [here](https://github.com/leanprover/lean/pull/1664).

* Merged `assert` and `note` tactics and renamed -> `have`.

* Renamed `pose` tactic -> `let`

* `assume` is now a real tactic that does not exit tactic mode.

* Modified `apply` tactic configuration object, and implemented [RFC #1342](https://github.com/leanprover/lean/issues/1342). It now has support for `auto_param` and `opt_param`. The new `eapply` tactic only creates subgoals for non dependent premises, and it simulates the behavior of the `apply` tactic in version 3.2.0.

* Add configuration object `rewrite_cfg` to `rw`/`rewrite` tactic. It now has support for `auto_param` and `opt_param`.
  The new goals are ordered using the same strategies available for `apply`.

* All `dsimp` tactics fail if they did not change anything.
  We can simulate the v3.2.0 using `dsimp {fail_if_unchaged := ff}` or `try dsimp`.

* `dsimp` does not unfold reducible definitions by default anymore.
  Example: `function.comp` applications will not be unfolded by default.
  We should use `dsimp [f]` if we want to reduce a reducible definition `f`.
  Another option is to use the new configuration parameter `unfold_reducible`.
  Example `dsimp {unfold_reducible := tt}`

* All `dunfold` and `unfold` tactics fail if they did not unfold anything.
  We can simulate the v3.2.0 using `unfold f {fail_if_unchaged := ff}` or `try {unfold f}`.

* `dunfold_occs` was deleted, the new `conv` tactical should be used instead.

* `unfold` tactic is now implemented on top of the `simp` tactics. So, we can use it to unfold
   declarations defined using well founded recursion. The `unfold1` variant does not unfold recursively,
   and it is shorthand for `unfold f {single_pass := tt}`.
   Remark: in v3.2.0, `unfold` was just an alias for the `dunfold` tactic.

* Deleted `simph` and `simp_using_hs` tactics. We should use `simp [*]` instead.

* Use `simp [-h]` and `dsimp [-h]` instead of `simp without h` and `dsimp without h`.
  Moreover, `simp [*, -h]` if `h` is a hypothesis, we are adding all hypotheses but `h`
  as additional simplification lemmas.

* Changed notation `rw [-h]` to `rw [← h]` to avoid confusion with the new `simp [-h]` notation.
  The ASCII version `rw [<- h]` is also supported.

* `rw [t] at *` now skips any hypothesis used by `t`. See discussion [here](https://github.com/leanprover/lean/issues/1813).

* Removed the redundant keywords `take` (replace with `assume`) and `suppose` (replace with the new anonymous `assume :`)

* Universes `max u v + 1` and `imax u v + 1` are now parsed as `(max u v) + 1` and `(imax u v) + 1`.

* Merged `generalize` and `generalize2` tactics into new `generalize id? : expr = id` tactic

* `standard.lean` has been removed. Any files that `import standard` can simply remove the line as
  most things that were once imported by this are now imported by default.

* The type classes for orders have been refactored to combine both the `(<)`
  and `(≤)` operations.  The new classes are `preorder`, `partial_order`, and
  `linear_order`.  The `partial_order` class corresponds to `weak_order`,
  `strict_order`, `order_pair`, and `strong_order_pair`.  The `linear_order`
  class corresponds to `linear_order_pair`, and `linear_strong_order_pair`.

* `injection` and `injections` tactics generate fresh names when user does not provide names.
  The fresh names are of the form `h_<idx>`. See discussion [here](https://github.com/leanprover/lean/issues/1805).

* Use `structure` to declare `and`. This change allows us to use `h.1` and `h.2` as shorthand for `h.left` and `h.right`.

* Add attribute `[pp_using_anonymous_constructor]` to `and`. Now, `and.intro h1 h2` is pretty printed as
  `⟨h1, h2⟩`. This change is motivated by the previous one. Without it, `and.intro h1 h2` would be
  pretty printed as `{left := h1, right := h2}`.

* User attributes can no longer be set with `set_basic_attribute`.  You need to use `user_attribute.set` now.

* The Emacs mode has been moved into its own repository and MELPA packages: https://github.com/leanprover/lean-mode

*API name changes*

* `list.dropn` => `list.drop`
* `list.taken` => `list.take`
* `tactic.dsimp` and `tactic.dsimp_core` => `tactic.dsimp_target`
* `tactic.dsimp_at_core` and `tactic.dsimp_at` => `tactic.dsimp_hyp`
* `tactic.delta_expr` => `tactic.delta`
* `tactic.delta` => `tactic.delta_target`
* `tactic.delta_at` => `tactic.delta_hyp`
* `tactic.simplify_goal` => `tactic.simp_target`
* `tactic.unfold_projection` => `tactic.unfold_proj`
* `tactic.unfold_projections_core` => `tactic.unfold_projs`
* `tactic.unfold_projections` => `tactic.unfold_projs_target`
* `tactic.unfold_projections_at` => `tactic.unfold_projs_hyp`
* `tactic.simp_intros_using`, `tactic.simph_intros_using`, `tactic.simp_intro_lst_using`, `tactic.simph_intro_lst_using` => `tactic.simp_intros`
* `tactic.simp_at` => `tactic.simp_hyp`
* deleted `tactic.simp_at_using`
* deleted `tactic.simph_at`

v3.2.0 (18 June 2017)
-------------

Lean is still evolving rapidly, and we apologize for the resulting instabilities. The lists below summarizes some of the new features and incompatibilities with respect to release 3.1.0.

*Features*

* Holes `{! ... !}` expressions and (user-defined) hole commands.
In Emacs, hole commands are executed using the keybinding C-c SPC.
The available commands can be found [here](https://github.com/leanprover/lean/blob/master/library/init/meta/hole_command.lean).

* The `leanpkg` package manager now manages projects and dependencies. See the documentation [here](https://github.com/leanprover/lean/tree/master/leanpkg). Parts of the standard library, like the superposition theorem prover `super`, have been moved to their own repositories. `.project` files are no longer needed to use `emacs` with projects.

* Well-founded recursion is now supported. (Details and examples for this and the next two items will soon appear in _Theorem Proving in Lean_.)

* Mutually (non meta) recursive definitions are now supported.

* Nested and mutual inductive data types are now supported.

* There is support for coinductive predicates.

* The `simp` tactic has been improved and supports more options, like wildcards. Hover over `simp` in an editor to see the documentation string (docstring).

* Additional interactive tactics have been added, and can be found [here](https://github.com/leanprover/lean/blob/master/library/init/meta/interactive.lean).

* A `case` tactic can now be used to structure proofs by cases and by induction. See [here](https://github.com/leanprover/lean/pull/1515).

* Various data structures, such as hash maps, have been added to the standard library [here](https://github.com/leanprover/lean/tree/master/library/data).

* There is preliminary support for user-defined parser extensions. More information can be found [here](https://github.com/leanprover/lean/pull/1617), and some examples can be found [here](https://github.com/leanprover/lean/blob/814a5edaf172c3835c000e3f631bddd85bd879ab/library/init/meta/interactive_base.lean#L184-L215).

* Numerous improvements have been made to the parallel compilation infrastructure and editor interfaces, for example, as described [here](https://github.com/leanprover/lean/pull/1405) and [here](https://github.com/leanprover/lean/pull/1534).

* There is a `transfer` method that can be used to transfer results e.g. to isomorphic structures; see [here](https://github.com/leanprover/lean/pull/1435).

* The monadic hierarchy now includes axioms for monadic classes. (See [here](https://github.com/leanprover/lean/pull/1485).)

* The tactic notation `tac ; [tac_1, ..., tac_n]` has been added.

* The type classes `has_well_founded`, `has_map`, `has_seq`, `has_orelse` have been added.

* Type classes can have input/output parameters. Some examples can be found [here](https://github.com/leanprover/lean/blob/master/library/init/core.lean).

* `tactic.run_io` can now be used to perform IO in tactics.

*Changes*

* Type class instances are not `[reducible]` by default anymore.

* Commands that produce output are now preceded by a hash symbol, as in `#check`, `#print`, `#eval` and `#reduce`. The `#eval` command calls the bytecode evaluator, and `#reduce` does definitional reduction in the kernel. Many instances of alternative syntax like `premise` for `variable` and `hypothesis` for `parameter` have been eliminated. See the discussion [here](https://github.com/leanprover/lean/issues/1432).

* The hierarchy of universes is now named `Sort 0`, `Sort 1`, `Sort 2`, and so on. `Prop` is alternative syntax for `Sort 0`, `Type` is alternative syntax for `Sort 1`, and `Type n` is alternative syntax for `Sort (n + 1)`. Many general constructors have been specialized from arbitrary `Sort`s to `Type` in order to simplify elaboration.

* Automatically generate dependent eliminators for inductive predicates.

* Improve unification hint matcher.

* Improve unifier. In function applications, explicit arguments are unified before implicit ones.
  Moreover, more aggresive unfolding is used when processing implicit arguments.

* Use `universe u` instead of `universe variable u` to declare a universe variable.

* The syntax `l^.map f` for projections is now deprecated in favor of `l.map f`.

* The behavior of the `show` tactic in interactive tactic mode has changed. It no longer leaves tactic mode. Also, it can now be used to select a goal other than the current one.

* The `assertv` and `definev` tactics have been eliminated in favor of `note` and `pose`.

* `has_andthen` type class is now heterogeneous,

* The encoding of structures has been changed, following the strategy described [here](https://github.com/leanprover/lean/wiki/Refactoring-structures). Generic operations like `add` and `mul` are replaced by `has_add.add` and `has_mul.mul`, respectively. One can provisionally obtain the old encodings with `set_option old_structure_cmd true
`.

* Syntax for quotations in metaprograms has changed. The notation `` `(t)`` elaborates `t` at definition time and produces an expression. The notation ``` ``(t) ``` resolves names at definition time produces a pre-expression, and ```` ```(t)```` resolves names at tactic execution time, and produces a pre-expression. Details can be found in the paper Ebner et al, _A Metaprogramming Framework for Formal Verification_.

* The types `expr` for expressions and `pexpr` for pre-expressions have been unified, so that `pexpr` is defined as `expr ff`. See [here](https://github.com/leanprover/lean/pull/1580).

* Handling of the `io` monad has changed. Examples can be found [here](https://github.com/leanprover/lean/tree/master/leanpkg/leanpkg) in the code for `leanpkg`, which is written in Lean itself.

- `state` and `state_t` are universe polymorphic.

* `option_map` and `option_bind` have been renamed to `option.map` and `option.bind`, respectively.

* GCC 7 compatibility

* Use single quotes for character literals (e.g., 'a').
