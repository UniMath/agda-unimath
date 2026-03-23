# Symmetric multilinear maps between left modules over rings

```agda
module multilinear-algebra.symmetric-multilinear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import lists.finite-sequences

open import multilinear-algebra.multilinear-maps-left-modules-rings

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Let `M` and `N` be two [left modules](linear-algebra.left-modules-rings.md) over
a [ring](ring-theory.rings.md) `R` and `n : ℕ` a
[natural number](elementary-number-theory.natural-numbers.md); a
[multilinear map](multilinear-algebra.multilinear-maps-left-modules-rings.md)
`f : Mⁿ⁺¹ → N` is called
{{#concept "symmetric" Disambiguation="multilinear map between left modules" Agda=is-symmetric-multilinear-map-left-module-Ring}}
if f is invariant under all
[permutations](finite-group-theory.permutations-standard-finite-types.md) of
[ℕₙ](univalent-combinatorics.standard-finite-types.md):

```text
∀ (σ : Aut ℕₙ) (u : Mⁿ⁺¹) → f (u ∘ σ) ＝ f u
```

## Definitions

### The property of being a symmetric multilinear map

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f : multilinear-map-left-module-Ring R M N n)
  where

  is-symmetric-prop-multilinear-map-left-module-Ring : Prop (l2 ⊔ l3)
  is-symmetric-prop-multilinear-map-left-module-Ring =
    Π-Prop
      ( Permutation (succ-ℕ n))
      ( λ σ →
        Π-Prop
          ( fin-sequence (type-left-module-Ring R M) (succ-ℕ n))
          ( λ u →
            Id-Prop
              ( set-left-module-Ring R N)
              ( map-multilinear-map-left-module-Ring R M N n f
                (u ∘ map-equiv σ))
              ( map-multilinear-map-left-module-Ring R M N n f u)))

  is-symmetric-multilinear-map-left-module-Ring : UU (l2 ⊔ l3)
  is-symmetric-multilinear-map-left-module-Ring =
    type-Prop is-symmetric-prop-multilinear-map-left-module-Ring

  is-prop-is-symmetric-multilinear-map-left-module-Ring :
    is-prop is-symmetric-multilinear-map-left-module-Ring
  is-prop-is-symmetric-multilinear-map-left-module-Ring =
    is-prop-type-Prop is-symmetric-prop-multilinear-map-left-module-Ring
```

### The type of symmetric multilinear maps between left modules

```agda
symmetric-multilinear-map-left-module-Ring :
  {l1 l2 l3 : Level} →
  (R : Ring l1) →
  (M : left-module-Ring l2 R) →
  (N : left-module-Ring l3 R) →
  (n : ℕ) →
  UU (l1 ⊔ l2 ⊔ l3)
symmetric-multilinear-map-left-module-Ring R M N n =
  type-subtype
    ( is-symmetric-prop-multilinear-map-left-module-Ring R M N n)

module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f : symmetric-multilinear-map-left-module-Ring R M N n)
  where

  map-symmetric-multilinear-map-left-module-Ring :
    fin-sequence (type-left-module-Ring R M) (succ-ℕ n) →
    type-left-module-Ring R N
  map-symmetric-multilinear-map-left-module-Ring =
    map-multilinear-map-left-module-Ring R M N n (pr1 f)

  is-multilinear-map-symmetric-multilinear-map-left-module-Ring :
    is-multilinear-map-left-module-Ring R M N n
      ( map-symmetric-multilinear-map-left-module-Ring)
  is-multilinear-map-symmetric-multilinear-map-left-module-Ring =
    is-multilinear-map-multilinear-map-left-module-Ring R M N n (pr1 f)

  is-symmetric-map-symmetric-multilinear-map-left-module-Ring :
    (σ : Permutation (succ-ℕ n)) →
    (u : fin-sequence (type-left-module-Ring R M) (succ-ℕ n)) →
    map-symmetric-multilinear-map-left-module-Ring (u ∘ map-equiv σ) ＝
    map-symmetric-multilinear-map-left-module-Ring u
  is-symmetric-map-symmetric-multilinear-map-left-module-Ring = pr2 f
```
