Low level format
================

Lean can export .lean files in a low-level format that is easy to parse and process.
The exported file contains only fully elaborated terms.
The file describes hierarchical names, universe levels and expressions.
These objects are used to declare inductive datatypes, definitions and axioms.

```
cd lean/library
lean --export=export.out --recursive
```

There are several checkers available that can read these files:
* [trepplein](https://github.com/gebner/trepplein), a type-checker written in Scala.
* [tc](https://github.com/dselsam/tc), a type-checker written in Haskell.
* [leanchecker](https://github.com/leanprover-community/lean/tree/master/src/checker), a bare-bones version of the Lean kernel.

Hierarchical names
------------------

A hierarchical name is essentially a list of strings and integers.
Each hierarchical name has a unique identifier: a unsigned integer.
The unsigned integer 0 denotes the _anonymous_ hierarchical name.
We can also view it as the empty name.
The following commands are used to define hierarchical names in the export file.

```
<nidx'> #NS <nidx> <string>
<nidx'> #NI <nidx> <integer>
```

In both commands, `nidx` is the unique identifier of an existing hierarchical name,
and `nidx'` is the identifier for the hierarchical name being defined.
The first command defines a hierarchical name by appending the given string,
and the second by appending the given integer.
The hierarchical name `foo.bla.1.boo` may be defined using the following sequence of commands

```
1 #NS 0 foo
2 #NS 1 bla
3 #NI 2 1
4 #NS 3 boo
```

Universe terms
---------------

Lean supports universe polymorphism.
That is, declaration in Lean can be parametrized by one or more universe level parameters.
The declarations can then be instantiated with universe level expressions.
In the standard Lean front-end, universe levels can be omitted, and the Lean elaborator (tries) to infer them automatically for users.
In this section, we describe the commands for create universe terms.
Each universe term has a unique identifier: a unsigned integer.
Note that the identifiers assigned to universe terms and hierarchical names are not disjoint.
The unsigned integer 0 is used to denote the universe 0.

The following commands are used to create universe terms in the export file.

```
<uidx'> #US  <uidx>
<uidx'> #UM  <uidx_1> <uidx_2>
<uidx'> #UIM <uidx_1> <uidx_2>
<uidx'> #UP  <nidx>
```

In the commands above, `uidx`, `uidx_1` and `uidx_2` denote the unique identifier of existing universe terms,
`nidx` the unique identifier of existing hierarchical names, and `nidx'` is the identifier for the universe
term being defined. The command `#US` defines the _successor_ universe for `uidx`, the `#UM` the maximum universe for `uidx_1` and `uidx_2`,
and `#UIM` is the "impredicative" maximum. It is defined as zero if `uidx_2` evaluates to zero, and `#UM` otherwise.
The command `#UP` defines the universe parameter with name `nidx`.
Here is the sequence of commands for creating the universe term `imax (max 2 l1) l2`.
```
1 #NS 0 l1
2 #NS 0 l2
1 #US 0
2 #US 1
3 #UP 1
4 #UP 2
5 #UM 2 3
6 #UIM 5 4
```
Thus, the unique identifier for term `imax (max 2 l1) l2` is `6`. The unique identifier for term `l1` is `3`.

Expressions
-----------

In Lean, we have the following kind of expressions:
variables, sorts (aka Type), constants, constants, function applications, lambdas, and dependent function spaces (aka Pis).
Each expression has a unique identifier: a unsigned integer.
Again, the expression unique identifiers are not disjoint from the universe term and hierarchical name ones.
The following command are used to create expressions in the export file.
```
<eidx'> #EV <integer>
<eidx'> #ES <uidx>
<eidx'> #EC <nidx> <uidx>*
<eidx'> #EA <eidx_1> <eidx_2>
<eidx'> #EL <info> <nidx> <eidx_1> <eidx_2>
<eidx'> #EP <info> <nidx> <eidx_1> <eidx_2>
```
In the commands above, `uidx` denotes the unique identifier of existing universe terms,
`nidx` the unique identifier of existing hierarchical names, `eidx_1` and `eidx_2` the unique
identifier of existing expressions, `info` is an annotation (explained later), and
`eidx'` is the identifier for the expression being defined.
The command `#EV` defines a bound variable with de Bruijn index `<integer>`.
The command `#ES` defines a sort using the given universe term.
The command `#EC` defines a constant with hierarchical name `nidx` and instantiated with 0 or more
universe terms `<uidx>*`.
The command `#EA` defines function application where `eidx_1` is the function, and `eidx_2` is the argument.
The binders of lambda and Pi abstractions are decorated with `info`.
This information has no semantic value for fully elaborated terms, but it is useful for pretty printing.
`info` can be one of the following annotations: `#BD`, `#BI`, `#BS` and `#BC`. The annotation `#BD` corresponds to
the default binder annotation `(...)` used in `.lean` files, and `#BI` to `{...}`, `#BS` to `{{...}}`, and
`#BC` to `[...]`.
The command `#EL` defines a lambda abstraction where `nidx` is the binder name, `eidx_1` the type, and
`eidx_2` the body. The command `#EP` is similar to `#EL`, but defines a Pi abstraction.
Here is the sequence of commands for creating the term `fun {A : Type.{1}} (a : A), a`
```
1 #NS 0 A
2 #NS 1 a
1 #US 0
1 #ES 1
2 #EV 0
3 #EL #BD 2 2 2
4 #EL #BI 1 1 3
```
Now, assume the environment contains the following constant declarations:
`nat : Type.{1}`, `nat.zero : nat`, `nat.succ : nat -> nat`, and `vector.{l} : Type.{l} -> nat -> Type.{max 1 l}`.
Then, the following sequence of commands can be used to create the term `vector.{1} nat 3`.
We annotate some commands with comments of the form `-- ...` to make the example easier to understand.
```
1 #NS 0 nat
2 #NS 1 zero
3 #NS 1 succ
4 #NS 0 vector
1 #US 0
1 #EC 2          -- nat.zero
2 #EC 3          -- nat.succ
3 #EA 2 1        -- nat.succ nat.zero
4 #EA 2 3        -- nat.succ (nat.succ nat.zero)
5 #EA 2 4        -- nat.succ (nat.succ (nat.succ nat.zero))
6 #EC 4 1        -- vector.{1}
7 #EC 1          -- nat
8 #EA 6 7        -- vector.{1} nat
9 #EA 8 5        -- vector.{1} nat (nat.succ (nat.succ (nat.succ nat.zero)))
```

Definitions and Axioms
----------------------

The command
```
#DEF <nidx> <eidx_1> <edix_2> <nidx*>
```
declares a definition with name `nidx` with zero or more universe parameters named `<nidx>*`.
The type is given by the expression `eidx_1` and the value by `eidx_2`.
Axioms are declared in a similar way
```
#AX <nidx> <eidx> <nidx*>
```
We are postulating the existence of an element with the given type.
The following command declare the `definition id.{l} {A : Type.{l}} (a : A) : A := a`.
```
2 #NS 0 id
3 #NS 0 l
4 #NS 0 A
1 #UP 3
0 #ES 1
5 #NS 0 a
1 #EV 0
2 #EV 1
3 #EP #BD 5 1 2
4 #EP #BI 4 0 3
5 #EL #BD 5 1 1
6 #EL #BD 4 0 5
#DEF 4 6 2 3
```

Inductive definitions
---------------------

Inductive definitions are given by the number of parameters, name, type,
introduction rules, and universe parameters.
```
#IND <num> <nidx> <eidx> <num_intros> <intro>* <nidx*>
```
Each `<intro>` is a pair of indices for the name and type of the introduction rule.

For example, consider the inductive data type of lists:
```lean
inductive {u} list (α : Type u) : Type u
| nil : list
| cons : α → list → list
```
It gets exported as the following commands (not showing constructions such as
`list.induction_on`, etc.):
```
1 #NS 0 u
2 #NS 0 list
3 #NS 0 α
1 #UP 1
0 #ES 1
1 #EP #BD 3 0 0
4 #NS 2 nil
2 #EC 2 1
3 #EV 0
4 #EA 2 3
5 #EP #BD 3 0 4
5 #NS 2 cons
6 #NS 0 a
6 #EV 1
7 #EA 2 6
8 #EV 2
9 #EA 2 8
10 #EP #BD 6 7 9
11 #EP #BD 6 3 10
12 #EP #BI 3 0 11
#IND 1 2 1 2 4 5 5 12 1
```

Quotient declaration
--------------------

The declaration of the quotient type and its computational rule is exported as
`#QUOT`.

Notation
--------

The export contains information about prefix, postfix, and infix notation,
where the head symbol is a constant.
These are indicated using the `#PREFIX`, `#POSTFIX`, and `#INFIX` commands.
They all follow the same syntax:

```
#PREFIX <name_idx> <precedence> <token>
```
