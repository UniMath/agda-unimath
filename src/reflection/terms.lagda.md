# Terms

```agda
module reflection.terms where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import foundation-core.cartesian-product-types

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
  variable-Term-Agda : ℕ → list (Argument-Agda Term-Agda) → Term-Agda
  -- An application of a constructor or definition
  constructor-Term-Agda : Name-Agda → list (Argument-Agda Term-Agda) → Term-Agda
  definition-Term-Agda : Name-Agda → list (Argument-Agda Term-Agda) → Term-Agda
  -- A lambda abstraction
  lambda-Term-Agda :
    Visibility-Argument-Agda → Abstraction-Agda Term-Agda → Term-Agda
  pattern-lambda-Term-Agda :
    list Clause-Agda → list (Argument-Agda Term-Agda) → Term-Agda
  -- A Pi term
  dependent-product-Term-Agda :
    Argument-Agda Term-Agda → Abstraction-Agda Term-Agda → Term-Agda
  -- A sort, also called a universe
  sort-Term-Agda : Sort-Agda → Term-Agda
  -- A literal, e.g. `3`
  literal-Term-Agda : Literal-Agda → Term-Agda
  -- A metavariable
  metavariable-Term-Agda :
    Metavariable-Agda → list (Argument-Agda Term-Agda) → Term-Agda
  -- A hole
  unknown-Term-Agda : Term-Agda

data Sort-Agda where
  -- A universe of a given (possibly neutral) level
  universe-Sort-Agda : Term-Agda → Sort-Agda
  -- A universe of a given concrete level
  fixed-universe-Sort-Agda : ℕ → Sort-Agda
  -- A Prop of a given (possibly neutral) level
  prop-Sort-Agda : Term-Agda → Sort-Agda
  -- A Prop of a given concrete level
  fixed-prop-Sort-Agda : ℕ → Sort-Agda
  -- UUωi of a given concrete level i.
  fixed-large-universe-Sort-Agda : ℕ → Sort-Agda
  -- A hole
  unknown-Sort-Agda : Sort-Agda

data Pattern-Agda where
  constructor-Term-Agda :
    Name-Agda → list (Argument-Agda Pattern-Agda) → Pattern-Agda
  dot-Pattern-Agda : Term-Agda → Pattern-Agda
  variable-Term-Agda : ℕ → Pattern-Agda
  literal-Term-Agda : Literal-Agda → Pattern-Agda
  projection-Pattern-Agda : Name-Agda → Pattern-Agda
  -- Absurd pattern with a de Bruijn index
  absurd-Pattern-Agda : ℕ → Pattern-Agda

-- A clause-Clause-Agda on a pattern matching lambda
data Clause-Agda where
  clause-Clause-Agda :
    Telescope-Agda → list (Argument-Agda Pattern-Agda) → Term-Agda → Clause-Agda
  absurd-Clause-Agda :
    Telescope-Agda → list (Argument-Agda Pattern-Agda) → Clause-Agda
```

## Bindings

```agda
{-# BUILTIN AGDATERM Term-Agda #-}
{-# BUILTIN AGDASORT Sort-Agda #-}
{-# BUILTIN AGDAPATTERN Pattern-Agda #-}
{-# BUILTIN AGDACLAUSE Clause-Agda #-}

{-# BUILTIN AGDATERMVAR variable-Term-Agda #-}
{-# BUILTIN AGDATERMCON constructor-Term-Agda #-}
{-# BUILTIN AGDATERMDEF definition-Term-Agda #-}
{-# BUILTIN AGDATERMMETA metavariable-Term-Agda #-}
{-# BUILTIN AGDATERMLAM lambda-Term-Agda #-}
{-# BUILTIN AGDATERMEXTLAM pattern-lambda-Term-Agda #-}
{-# BUILTIN AGDATERMPI dependent-product-Term-Agda #-}
{-# BUILTIN AGDATERMSORT sort-Term-Agda #-}
{-# BUILTIN AGDATERMLIT literal-Term-Agda #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown-Term-Agda #-}

{-# BUILTIN AGDASORTSET universe-Sort-Agda #-}
{-# BUILTIN AGDASORTLIT fixed-universe-Sort-Agda #-}
{-# BUILTIN AGDASORTPROP prop-Sort-Agda #-}
{-# BUILTIN AGDASORTPROPLIT fixed-prop-Sort-Agda #-}
{-# BUILTIN AGDASORTINF fixed-large-universe-Sort-Agda #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown-Sort-Agda #-}

{-# BUILTIN AGDAPATCON constructor-Term-Agda #-}
{-# BUILTIN AGDAPATDOT dot-Pattern-Agda #-}
{-# BUILTIN AGDAPATVAR variable-Term-Agda #-}
{-# BUILTIN AGDAPATLIT literal-Term-Agda #-}
{-# BUILTIN AGDAPATPROJ projection-Pattern-Agda #-}
{-# BUILTIN AGDAPATABSURD absurd-Pattern-Agda #-}

{-# BUILTIN AGDACLAUSECLAUSE clause-Clause-Agda #-}
{-# BUILTIN AGDACLAUSEABSURD absurd-Clause-Agda #-}
```

## Helpers

```agda
replicate-hidden-Argument-Agda : ℕ → list (Argument-Agda Term-Agda)
replicate-hidden-Argument-Agda zero-ℕ =
  nil
replicate-hidden-Argument-Agda (succ-ℕ n) =
  cons
    ( hidden-Argument-Agda (unknown-Term-Agda))
    ( replicate-hidden-Argument-Agda n)
```
