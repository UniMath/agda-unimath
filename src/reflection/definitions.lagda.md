# Definitions

```agda
module reflection.definitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

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
  function : (cs : list Clause-Agda) → Definition-Agda
  data-type : (pars : ℕ) (cs : list Name-Agda) → Definition-Agda
  record-type :
    (c : Name-Agda) (fs : list (Argument-Agda Name-Agda)) → Definition-Agda
  data-cons : (d : Name-Agda) → Definition-Agda
  axiom : Definition-Agda
  prim-fun : Definition-Agda
{-# BUILTIN AGDADEFINITION Definition-Agda #-}
{-# BUILTIN AGDADEFINITIONFUNDEF function #-}
{-# BUILTIN AGDADEFINITIONDATADEF data-type #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF record-type #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE axiom #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE prim-fun #-}
```

## Examples

### Constructors and definitions

```agda
_ : quoteTerm ℕ ＝ def (quote ℕ) nil
_ = refl

_ :
  quoteTerm (succ-ℕ zero-ℕ) ＝
  con
    ( quote succ-ℕ)
    ( unit-list (visible-Argument-Agda (con (quote zero-ℕ) nil)))
_ = refl

_ :
  {l : Level} {A : UU l} →
  quoteTerm (type-trunc-Prop A) ＝
  def
    ( quote type-trunc-Prop)
    ( cons
      ( hidden-Argument-Agda (var 1 nil))
      ( unit-list (visible-Argument-Agda (var 0 nil))))
_ = refl
```

### Lambda abstractions

```agda
_ :
  quoteTerm (λ (x : ℕ) → x) ＝ lam visible (abs "x" (var 0 nil))
_ = refl

_ :
  quoteTerm (λ {x : ℕ} (y : ℕ) → x) ＝
  lam hidden (abs "x" (lam visible (abs "y" (var 1 nil))))
_ = refl

private
  helper : (A : UU lzero) → A → A
  helper A x = x

  _ :
    quoteTerm (helper (ℕ → ℕ) (λ { zero-ℕ → zero-ℕ ; (succ-ℕ x) → x})) ＝
    def
      ( quote helper)
      ( cons
        -- ℕ → ℕ
        ( visible-Argument-Agda
          ( pi
            ( visible-Argument-Agda (def (quote ℕ) nil))
            ( abs "_" (def (quote ℕ) nil))))
        ( unit-list
          -- The pattern matching lambda
          ( visible-Argument-Agda
            ( pat-lam
              ( cons
                -- zero-ℕ clause
                ( clause
                  -- No telescope
                  ( nil)
                  -- Left side of the first lambda case
                  ( unit-list (visible-Argument-Agda (con (quote zero-ℕ) nil)))
                  -- Right side of the first lambda case
                  ( con (quote zero-ℕ) nil))
                ( unit-list
                  -- succ-ℕ clause
                  ( clause
                    -- Telescope-Agda matching the "x"
                    ( unit-list
                      ( "x" , visible-Argument-Agda (def (quote ℕ) nil)))
                    -- Left side of the second lambda case
                    ( unit-list
                      ( visible-Argument-Agda
                        ( con
                          ( quote succ-ℕ)
                          ( unit-list ( visible-Argument-Agda (var 0))))))
                    -- Right side of the second lambda case
                    ( var 0 nil))))
              ( nil)))))
  _ = refl

  _ :
    quoteTerm (helper (empty → ℕ) (λ ())) ＝
    def
      ( quote helper)
      ( cons
        ( visible-Argument-Agda
          ( pi (visible-Argument-Agda (def (quote empty) nil))
          ( abs "_" (def (quote ℕ) nil))))
        ( unit-list
          ( visible-Argument-Agda
            -- Lambda
            ( pat-lam
              ( unit-list
                -- Clause-Agda
                ( absurd-clause
                  ( unit-list
                    ( "()" , visible-Argument-Agda (def (quote empty) nil)))
                  ( unit-list
                    ( visible-Argument-Agda (absurd 0)))))
              ( nil)))))
  _ = refl
```

### Pi terms

```agda
_ : quoteTerm (ℕ → ℕ) ＝
    pi
      ( visible-Argument-Agda (def (quote ℕ) nil))
      ( abs "_" (def (quote ℕ) nil))
_ = refl

_ : quoteTerm ((x : ℕ) → is-zero-ℕ x) ＝
    pi
      ( visible-Argument-Agda (def (quote ℕ) nil))
      ( abs "x"
        ( def
          ( quote is-zero-ℕ)
          ( cons
            ( visible-Argument-Agda (var 0 nil))
            ( nil))))
_ = refl
```

### Universes

```agda
_ : {l : Level} → quoteTerm (UU l) ＝ agda-sort (set (var 0 nil))
_ = refl

_ : quoteTerm (UU (lsuc lzero)) ＝ agda-sort (lit 1)
_ = refl

_ : quoteTerm (UUω) ＝ agda-sort (inf 0)
_ = refl
```

### Literals

```agda
_ : quoteTerm 3 ＝ lit (nat 3)
_ = refl

_ : quoteTerm "hello" ＝ lit (string "hello")
_ = refl
```
