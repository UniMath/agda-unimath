# Definitions

```agda
module reflection.definitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.identity-types

open import lists.lists

open import reflection.abstractions
open import reflection.arguments
open import reflection.literals
open import reflection.names
open import reflection.terms
```

</details>

## Idea

The `Definition-Agda` type represents a definition in Agda.

## Definition

```agda
data Definition-Agda : UU lzero where

  function-Definition-Agda :
    list Clause-Agda → Definition-Agda

  data-type-Definition-Agda :
    ℕ → list Name-Agda → Definition-Agda

  record-type-Definition-Agda :
    Name-Agda → list (Argument-Agda Name-Agda) → Definition-Agda

  data-constructor-Definition-Agda :
    Name-Agda → Quantity-Argument-Agda → Definition-Agda

  postulate-Definition-Agda :
    Definition-Agda

  primitive-function-Definition-Agda :
    Definition-Agda
```

## Bindings

```agda
{-# BUILTIN AGDADEFINITION Definition-Agda #-}
{-# BUILTIN AGDADEFINITIONFUNDEF function-Definition-Agda #-}
{-# BUILTIN AGDADEFINITIONDATADEF data-type-Definition-Agda #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF record-type-Definition-Agda #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-constructor-Definition-Agda #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE postulate-Definition-Agda #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE primitive-function-Definition-Agda #-}
```

## Examples

### Constructors and definitions

```agda
_ : quoteTerm ℕ ＝ definition-Term-Agda (quote ℕ) nil
_ = refl

_ :
  quoteTerm (succ-ℕ zero-ℕ) ＝
  constructor-Term-Agda
    ( quote succ-ℕ)
    ( unit-list
      ( visible-Argument-Agda (constructor-Term-Agda (quote zero-ℕ) nil)))
_ = refl

-- _ :
--   {l : Level} {A : UU l} →
--   quoteTerm (type-trunc-Prop A) ＝
--   definition-Term-Agda
--     ( quote type-trunc-Prop)
--     ( cons
--       ( hidden-Argument-Agda (variable-Term-Agda 1 nil))
--       ( unit-list (visible-Argument-Agda (variable-Term-Agda 0 nil))))
-- _ = refl
```

### Lambda abstractions

```agda
_ :
  quoteTerm (λ (x : ℕ) → x) ＝
  lambda-Term-Agda visible-Visibility-Argument-Agda
    ( cons-Abstraction-Agda "x" (variable-Term-Agda 0 nil))
_ = refl

_ :
  quoteTerm (λ {x : ℕ} (y : ℕ) → x) ＝
  lambda-Term-Agda hidden-Visibility-Argument-Agda
    ( cons-Abstraction-Agda
      ( "x")
      ( lambda-Term-Agda visible-Visibility-Argument-Agda
        ( cons-Abstraction-Agda "y" (variable-Term-Agda 1 nil))))
_ = refl

private
  helper : (A : UU lzero) → A → A
  helper A x = x

  _ :
    quoteTerm (helper (ℕ → ℕ) (λ { zero-ℕ → zero-ℕ ; (succ-ℕ x) → x})) ＝
    definition-Term-Agda
      ( quote helper)
      ( cons
        -- ℕ → ℕ
        ( visible-Argument-Agda
          ( dependent-product-Term-Agda
            ( visible-Argument-Agda (definition-Term-Agda (quote ℕ) nil))
            ( cons-Abstraction-Agda "_" (definition-Term-Agda (quote ℕ) nil))))
        ( unit-list
          -- The pattern matching lambda
          ( visible-Argument-Agda
            ( pattern-lambda-Term-Agda
              ( cons
                -- zero-ℕ clause-Clause-Agda
                ( clause-Clause-Agda
                  -- No telescope
                  ( nil)
                  -- Left side of the first lambda case
                  ( unit-list
                    ( visible-Argument-Agda
                      ( constructor-Term-Agda (quote zero-ℕ) nil)))
                  -- Right side of the first lambda case
                  ( constructor-Term-Agda (quote zero-ℕ) nil))
                ( unit-list
                  -- succ-ℕ clause-Clause-Agda
                  ( clause-Clause-Agda
                    -- Telescope-Agda matching the "x"
                    ( unit-list
                      ( "x" ,
                        visible-Argument-Agda
                          ( definition-Term-Agda (quote ℕ) nil)))
                    -- Left side of the second lambda case
                    ( unit-list
                      ( visible-Argument-Agda
                        ( constructor-Term-Agda
                          ( quote succ-ℕ)
                          ( unit-list
                            ( visible-Argument-Agda (variable-Term-Agda 0))))))
                    -- Right side of the second lambda case
                    ( variable-Term-Agda 0 nil))))
              ( nil)))))
  _ = refl

  _ :
    quoteTerm (helper (empty → ℕ) (λ ())) ＝
    definition-Term-Agda
      ( quote helper)
      ( cons
        ( visible-Argument-Agda
          ( dependent-product-Term-Agda
            ( visible-Argument-Agda (definition-Term-Agda (quote empty) nil))
          ( cons-Abstraction-Agda "_" (definition-Term-Agda (quote ℕ) nil))))
        ( unit-list
          ( visible-Argument-Agda
            -- Lambda
            ( pattern-lambda-Term-Agda
              ( unit-list
                -- Clause-Agda
                ( absurd-Clause-Agda
                  ( unit-list
                    ( "()" ,
                      visible-Argument-Agda
                        ( definition-Term-Agda (quote empty) nil)))
                  ( unit-list
                    ( visible-Argument-Agda (absurd-Pattern-Agda 0)))))
              ( nil)))))
  _ = refl
```

### Pi terms

```agda
_ : quoteTerm (ℕ → ℕ) ＝
    dependent-product-Term-Agda
      ( visible-Argument-Agda (definition-Term-Agda (quote ℕ) nil))
      ( cons-Abstraction-Agda "_" (definition-Term-Agda (quote ℕ) nil))
_ = refl

_ : quoteTerm ((x : ℕ) → is-zero-ℕ x) ＝
    dependent-product-Term-Agda
      ( visible-Argument-Agda (definition-Term-Agda (quote ℕ) nil))
      ( cons-Abstraction-Agda "x"
        ( definition-Term-Agda
          ( quote is-zero-ℕ)
          ( cons
            ( visible-Argument-Agda (variable-Term-Agda 0 nil))
            ( nil))))
_ = refl
```

### Universes

```agda
_ :
  {l : Level} →
  quoteTerm (UU l) ＝
  sort-Term-Agda (universe-Sort-Agda (variable-Term-Agda 0 nil))
_ = refl

_ : quoteTerm (UU (lsuc lzero)) ＝ sort-Term-Agda (fixed-universe-Sort-Agda 1)
_ = refl

_ : quoteTerm (UUω) ＝ sort-Term-Agda (fixed-large-universe-Sort-Agda 0)
_ = refl
```

### Literals

```agda
_ : quoteTerm 3 ＝ literal-Term-Agda (nat-Literal-Agda 3)
_ = refl

_ : quoteTerm "hello" ＝ literal-Term-Agda (string-Literal-Agda "hello")
_ = refl
```
