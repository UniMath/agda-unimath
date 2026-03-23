# Antisymmetric multilinear maps between left modules over rings

```agda
module multilinear-algebra.antisymmetric-multilinear-maps-left-modules-rings where
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
open import foundation.negated-equality
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
open import lists.replace-at-index-finite-sequences

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
{{#concept "antisymmetric" Disambiguation="multilinear map between left modules" Agda=is-antisymmetric-multilinear-map-left-module-Ring}}
if for any [indices](univalent-combinatorics.standard-finite-types.md)
`(i ≠ j : ℕₙ)`, `f ∘ ρᵢⱼ ~ - f`, where `ρᵢⱼ` extracts the coordinate at `j` and
put it at `i`:

```text
  ∀ ((xₒ,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xⱼ₋₁,xⱼ,xⱼ₊₁,...,xₙ) : Mⁿ⁺¹) →
  f (xₒ,...xᵢ₋₁,xⱼ,xᵢ,xᵢ₊₁,...,xⱼ₋₁,xⱼ₊₁,...,xₙ) ＝
  - f (xₒ,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xⱼ₋₁,xⱼ,xⱼ₊₁,...,xₙ)
```

## Definitions

### The property of being a antisymmetric multilinear map

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f : multilinear-map-left-module-Ring R M N n)
  where

  is-antisymmetric-prop-multilinear-map-left-module-Ring : Prop (l2 ⊔ l3)
  is-antisymmetric-prop-multilinear-map-left-module-Ring =
    Π-Prop
      ( Fin (succ-ℕ n))
      ( λ i →
        Π-Prop
          ( Fin (succ-ℕ n))
          ( λ j →
            Π-Prop
              ( i ≠ j)
              ( λ i≠j →
                Π-Prop
                  ( fin-sequence (type-left-module-Ring R M) (succ-ℕ n))
                  ( λ u →
                    Id-Prop
                      ( set-left-module-Ring R N)
                      ( map-multilinear-map-left-module-Ring R M N n f
                        ( replace-at-finite-sequence n i j u))
                      ( neg-left-module-Ring R N
                        ( map-multilinear-map-left-module-Ring R M N n f u))))))

  is-antisymmetric-multilinear-map-left-module-Ring : UU (l2 ⊔ l3)
  is-antisymmetric-multilinear-map-left-module-Ring =
    type-Prop is-antisymmetric-prop-multilinear-map-left-module-Ring

  is-prop-is-antisymmetric-multilinear-map-left-module-Ring :
    is-prop is-antisymmetric-multilinear-map-left-module-Ring
  is-prop-is-antisymmetric-multilinear-map-left-module-Ring =
    is-prop-type-Prop is-antisymmetric-prop-multilinear-map-left-module-Ring
```

### The type of antisymmetric multilinear maps between left modules

```agda
antisymmetric-multilinear-map-left-module-Ring :
  {l1 l2 l3 : Level} →
  (R : Ring l1) →
  (M : left-module-Ring l2 R) →
  (N : left-module-Ring l3 R) →
  (n : ℕ) →
  UU (l1 ⊔ l2 ⊔ l3)
antisymmetric-multilinear-map-left-module-Ring R M N n =
  type-subtype
    ( is-antisymmetric-prop-multilinear-map-left-module-Ring R M N n)

module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f : antisymmetric-multilinear-map-left-module-Ring R M N n)
  where

  map-antisymmetric-multilinear-map-left-module-Ring :
    fin-sequence (type-left-module-Ring R M) (succ-ℕ n) →
    type-left-module-Ring R N
  map-antisymmetric-multilinear-map-left-module-Ring =
    map-multilinear-map-left-module-Ring R M N n (pr1 f)

  is-multilinear-map-antisymmetric-multilinear-map-left-module-Ring :
    is-multilinear-map-left-module-Ring R M N n
      ( map-antisymmetric-multilinear-map-left-module-Ring)
  is-multilinear-map-antisymmetric-multilinear-map-left-module-Ring =
    is-multilinear-map-multilinear-map-left-module-Ring R M N n (pr1 f)

  is-antisymmetric-map-antisymmetric-multilinear-map-left-module-Ring :
    (i j : Fin (succ-ℕ n)) →
    (i≠j : i ≠ j) →
    (u : fin-sequence (type-left-module-Ring R M) (succ-ℕ n)) →
    map-antisymmetric-multilinear-map-left-module-Ring
      ( replace-at-finite-sequence n i j u) ＝
    neg-left-module-Ring R N
      ( map-antisymmetric-multilinear-map-left-module-Ring u)
  is-antisymmetric-map-antisymmetric-multilinear-map-left-module-Ring = pr2 f
```
