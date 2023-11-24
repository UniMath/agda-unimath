# Monoid actions

```agda
module group-theory.monoid-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.endomorphisms
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
```

</details>

## Idea

A **monoid action** of a [monoid](group-theory.monoids.md) `M` on a
[set](foundation-core.sets.md) `X` is a
[monoid homomorphism](group-theory.homomorphisms-monoids.md) from `M` into the
monoid of [endomorphisms](foundation.endomorphisms.md) `X → X`. The fact that
monoid homomorphisms preserve the monoid operation and the unit implies that a
monoid action `μ` of `M` on `X` satisfies the following laws:

```text
  μ mn x ＝ μ m (μ n x)
   μ 1 x ＝ x.
```

## Definition

### Monoid actions

```agda
action-Monoid : {l1 : Level} (l : Level) (M : Monoid l1) → UU (l1 ⊔ lsuc l)
action-Monoid l M = Σ (Set l) (λ X → hom-Monoid M (endo-Monoid X))

module _
  {l1 l2 : Level} (M : Monoid l1) (X : action-Monoid l2 M)
  where

  set-action-Monoid : Set l2
  set-action-Monoid = pr1 X

  type-action-Monoid : UU l2
  type-action-Monoid = type-Set set-action-Monoid

  is-set-type-action-Monoid : is-set type-action-Monoid
  is-set-type-action-Monoid = is-set-type-Set set-action-Monoid

  mul-hom-monoid-action-Monoid : hom-Monoid M (endo-Monoid set-action-Monoid)
  mul-hom-monoid-action-Monoid = pr2 X

  mul-action-Monoid : type-Monoid M → type-action-Monoid → type-action-Monoid
  mul-action-Monoid =
    map-hom-Monoid M
      ( endo-Monoid set-action-Monoid)
      ( mul-hom-monoid-action-Monoid)

  ap-mul-action-Monoid :
    {m : type-Monoid M} {x y : type-action-Monoid} →
    x ＝ y → mul-action-Monoid m x ＝ mul-action-Monoid m y
  ap-mul-action-Monoid {m} = ap (mul-action-Monoid m)

  ap-mul-action-Monoid' :
    {m n : type-Monoid M} (p : m ＝ n) {x : type-action-Monoid} →
    mul-action-Monoid m x ＝ mul-action-Monoid n x
  ap-mul-action-Monoid' p {x} = ap (λ t → mul-action-Monoid t x) p

  associative-mul-action-Monoid :
    (x y : type-Monoid M) (z : type-action-Monoid) →
    mul-action-Monoid (mul-Monoid M x y) z ＝
    mul-action-Monoid x (mul-action-Monoid y z)
  associative-mul-action-Monoid x y =
    htpy-eq
      ( preserves-mul-hom-Monoid M
        ( endo-Monoid set-action-Monoid)
        ( mul-hom-monoid-action-Monoid))

  unit-law-mul-action-Monoid :
    (x : type-action-Monoid) → mul-action-Monoid (unit-Monoid M) x ＝ x
  unit-law-mul-action-Monoid =
    htpy-eq
      ( preserves-unit-hom-Monoid M
        ( endo-Monoid set-action-Monoid)
        ( mul-hom-monoid-action-Monoid))
```
