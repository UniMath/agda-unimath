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
type `Term-Agda`. See the comments for details on the constructors.

We can obtain a `Term-Agda` from an agda term through the keyword `quoteTerm`.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definition

```agda
data Term-Agda : UU lzero
data Sort-Agda : UU lzero
data Pattern-Agda : UU lzero
data Clause-Agda : UU lzero
Telescope-Agda = list (String × Argument-Agda Term-Agda)

data Term-Agda where
  -- Variables, where the natural number is a de Bruijn index
  var : (x : ℕ) (args : list (Argument-Agda Term-Agda)) → Term-Agda
  -- An application of a constructor or definition
  con : (c : Name-Agda) (args : list (Argument-Agda Term-Agda)) → Term-Agda
  def : (f : Name-Agda) (args : list (Argument-Agda Term-Agda)) → Term-Agda
  -- A lambda abstraction
  lam :
    (v : Visibility-Argument-Agda) (t : Abstraction-Agda Term-Agda) → Term-Agda
  pat-lam :
    (cs : list Clause-Agda) (args : list (Argument-Agda Term-Agda)) → Term-Agda
  -- A Pi term
  pi :
    (a : Argument-Agda Term-Agda) (b : Abstraction-Agda Term-Agda) → Term-Agda
  -- A sort, also called a universe
  agda-sort : (s : Sort-Agda) → Term-Agda
  -- A literal, e.g. `3`
  lit : (l : Literal-Agda) → Term-Agda
  -- A metavariable
  meta : (x : Metavariable-Agda) → list (Argument-Agda Term-Agda) → Term-Agda
  -- A hole
  unknown : Term-Agda

data Sort-Agda where
  -- A universe of a given (possibly neutral) level
  set : (t : Term-Agda) → Sort-Agda
  -- A universe of a given concrete level
  lit : (n : ℕ) → Sort-Agda
  -- A Prop of a given (possibly neutral) level
  prop : (t : Term-Agda) → Sort-Agda
  -- A Prop of a given concrete level
  propLit : (n : ℕ) → Sort-Agda
  -- UUωi of a given concrete level i.
  inf : (n : ℕ) → Sort-Agda
  -- A hole
  unknown : Sort-Agda

data Pattern-Agda where
  con : (c : Name-Agda) (ps : list (Argument-Agda Pattern-Agda)) → Pattern-Agda
  dot : (t : Term-Agda) → Pattern-Agda
  var : (x : ℕ) → Pattern-Agda
  lit : (l : Literal-Agda) → Pattern-Agda
  proj : (f : Name-Agda) → Pattern-Agda
  -- Absurd pattern with a de Bruijn index
  absurd : (x : ℕ) → Pattern-Agda

-- A clause on a pattern matching lambda
data Clause-Agda where
  clause :
    (tel : Telescope-Agda)
    (ps : list (Argument-Agda Pattern-Agda))
    (t : Term-Agda) →
    Clause-Agda
  absurd-clause :
    (tel : Telescope-Agda)
    (ps : list (Argument-Agda Pattern-Agda)) →
    Clause-Agda
```

<details><summary>Bindings</summary>

```agda
{-# BUILTIN AGDATERM Term-Agda #-}
{-# BUILTIN AGDASORT Sort-Agda #-}
{-# BUILTIN AGDAPATTERN Pattern-Agda #-}
{-# BUILTIN AGDACLAUSE Clause-Agda #-}

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
replicate-hidden-Argument-Agda : ℕ → list (Argument-Agda Term-Agda)
replicate-hidden-Argument-Agda zero-ℕ = nil
replicate-hidden-Argument-Agda (succ-ℕ n) =
  cons (hidden-Argument-Agda (unknown)) (replicate-hidden-Argument-Agda n)
```
