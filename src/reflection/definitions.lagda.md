# Definitions

```agda
module reflection.definitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.characters
open import foundation.floats
open import foundation.identity-types
open import foundation.machine-integers
open import foundation.propositional-truncations
open import foundation.strings
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.dependent-pair-types

open import group-theory.precategory-of-groups

open import lists.lists

open import reflection.abstractions
open import reflection.arguments
open import reflection.fixity
open import reflection.literals
open import reflection.metavariables
open import reflection.names
open import reflection.terms

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

-- TODO

## Definition

```agda
data Definition : UU lzero where
  function    : (cs : list Clause) → Definition
  data-type   : (pars : ℕ) (cs : list Name) → Definition
  record-type : (c : Name) (fs : list (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition
{-# BUILTIN AGDADEFINITION                Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}
```

## Examples

```agda
_ : quoteTerm ℕ ＝ def (quote ℕ) nil
_ = refl

_ :
  quoteTerm (λ (x : ℕ) → x) ＝ lam visible (abs "x" (var 0 nil))
_ = refl

_ :
  quoteTerm (Fin 2) ＝
  def
    ( quote Fin)
    ( cons
      ( arg
        ( arg-info visible (modality relevant quantity-ω))
        ( lit (nat 2)))
      ( nil))
_ = refl

_ :
  {l : Level} {A : UU l} →
  quoteTerm (type-trunc-Prop A) ＝
  def
    ( quote type-trunc-Prop)
    ( cons
      ( arg
        ( arg-info hidden (modality relevant quantity-ω))
      ( var 1 nil))
      ( cons
        ( arg
          ( arg-info visible (modality relevant quantity-ω))
          (var 0 nil))
        ( nil)))
_ = refl

_ :
  quoteTerm (UU (lsuc lzero)) ＝ agda-sort (lit 1)
_ = refl

_ :
  quoteTerm Group-Large-Precat ＝ def (quote Group-Large-Precat) nil
_ = refl
```
