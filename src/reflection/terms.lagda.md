# Terms

```agda
module reflection.terms where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.universe-levels

open import lists.lists

open import primitives.strings

open import reflection.abstractions
open import reflection.arguments
open import reflection.literals
open import reflection.metavariables
open import reflection.names
```

</details>

## Idea

In this module we represent the terms of agda by an inductive definition of the
type `Term`. See the comments for details on the constructors.

We can obtain a `Term` from an agda term through the keyword `quoteTerm`.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definition

```agda
data Term : UU lzero
data Sort : UU lzero
data Pattern : UU lzero
data Clause : UU lzero
Telescope = list (String × Arg Term)

data Term where
  -- Variables, where the natural number is a de Bruijn index
  var : (x : ℕ) (args : list (Arg Term)) → Term
  -- An application of a constructor or definition
  con : (c : Name) (args : list (Arg Term)) → Term
  def : (f : Name) (args : list (Arg Term)) → Term
  -- A lambda abstraction
  lam : (v : Visibility) (t : Abs Term) → Term
  pat-lam : (cs : list Clause) (args : list (Arg Term)) → Term
  -- A Pi term
  pi : (a : Arg Term) (b : Abs Term) → Term
  -- A sort, also called a universe
  agda-sort : (s : Sort) → Term
  -- A literal, e.g. `3`
  lit : (l : Literal) → Term
  -- A metavariable
  meta : (x : Meta) → list (Arg Term) → Term
  -- A hole
  unknown : Term

data Sort where
  -- A universe of a given (possibly neutral) level
  set : (t : Term) → Sort
  -- A universe of a given concrete level
  lit : (n : ℕ) → Sort
  -- A Prop of a given (possibly neutral) level
  prop : (t : Term) → Sort
  -- A Prop of a given concrete level
  propLit : (n : ℕ) → Sort
  -- UUωi of a given concrete level i.
  inf : (n : ℕ) → Sort
  -- A hole
  unknown : Sort

data Pattern where
  con : (c : Name) (ps : list (Arg Pattern)) → Pattern
  dot : (t : Term) → Pattern
  var : (x : ℕ) → Pattern
  lit : (l : Literal) → Pattern
  proj : (f : Name) → Pattern
  -- Absurd pattern with a de Bruijn index
  absurd : (x : ℕ) → Pattern

-- A clause on a pattern matching lambda
data Clause where
  clause :
    (tel : Telescope) (ps : list (Arg Pattern)) (t : Term) → Clause
  absurd-clause :
    (tel : Telescope) (ps : list (Arg Pattern)) → Clause
```

<details><summary>Bindings</summary>

```agda
{-# BUILTIN AGDATERM Term #-}
{-# BUILTIN AGDASORT Sort #-}
{-# BUILTIN AGDAPATTERN Pattern #-}
{-# BUILTIN AGDACLAUSE Clause #-}

{-# BUILTIN AGDATERMVAR var #-}
{-# BUILTIN AGDATERMCON con #-}
{-# BUILTIN AGDATERMDEF def #-}
{-# BUILTIN AGDATERMMETA meta #-}
{-# BUILTIN AGDATERMLAM lam #-}
{-# BUILTIN AGDATERMEXTLAM pat-lam #-}
{-# BUILTIN AGDATERMPI pi #-}
{-# BUILTIN AGDATERMSORT agda-sort #-}
{-# BUILTIN AGDATERMLIT lit #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}

{-# BUILTIN AGDASORTSET set #-}
{-# BUILTIN AGDASORTLIT lit #-}
{-# BUILTIN AGDASORTPROP prop #-}
{-# BUILTIN AGDASORTPROPLIT propLit #-}
{-# BUILTIN AGDASORTINF inf #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

{-# BUILTIN AGDAPATCON con #-}
{-# BUILTIN AGDAPATDOT dot #-}
{-# BUILTIN AGDAPATVAR var #-}
{-# BUILTIN AGDAPATLIT lit #-}
{-# BUILTIN AGDAPATPROJ proj #-}
{-# BUILTIN AGDAPATABSURD absurd #-}

{-# BUILTIN AGDACLAUSECLAUSE clause #-}
{-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}
```

</details>

## Helpers

```agda
replicate-hidden-Arg : ℕ → list (Arg Term)
replicate-hidden-Arg zero-ℕ = nil
replicate-hidden-Arg (succ-ℕ n) =
  cons (hidden-Arg (unknown)) (replicate-hidden-Arg n)
```
