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

A [monoid](group-theory.monoids.md) `M` can **act** on a
[set](foundation-core.sets.md) `A` by a
[monoid homomorphism](group-theory.homomorphisms-monoids.md) `hom M (A → A)`.

## Definition

### Monoid actions

```agda
Monoid-Action : {l1 : Level} (l : Level) (M : Monoid l1) → UU (l1 ⊔ lsuc l)
Monoid-Action l M = Σ (Set l) (λ X → type-hom-Monoid M (endo-Monoid X))

module _
  {l1 l2 : Level} (M : Monoid l1) (X : Monoid-Action l2 M)
  where

  set-Monoid-Action : Set l2
  set-Monoid-Action = pr1 X

  type-Monoid-Action : UU l2
  type-Monoid-Action = type-Set set-Monoid-Action

  is-set-type-Monoid-Action : is-set type-Monoid-Action
  is-set-type-Monoid-Action = is-set-type-Set set-Monoid-Action

  mul-Monoid-Action : type-Monoid M → type-Monoid-Action → type-Monoid-Action
  mul-Monoid-Action = pr1 (pr1 (pr2 X))

  ap-mul-Monoid-Action :
    {m : type-Monoid M} {x y : type-Monoid-Action} →
    Id x y → Id (mul-Monoid-Action m x) (mul-Monoid-Action m y)
  ap-mul-Monoid-Action {m} = ap (mul-Monoid-Action m)

  ap-mul-Monoid-Action' :
    {m n : type-Monoid M} (p : Id m n) {x : type-Monoid-Action} →
    Id (mul-Monoid-Action m x) (mul-Monoid-Action n x)
  ap-mul-Monoid-Action' p {x} =
    ap (λ t → mul-Monoid-Action t x) p

  associative-mul-Monoid-Action :
    (x y : type-Monoid M) (z : type-Monoid-Action) →
    Id
      ( mul-Monoid-Action (mul-Monoid M x y) z)
      ( mul-Monoid-Action x (mul-Monoid-Action y z))
  associative-mul-Monoid-Action x y = htpy-eq (pr2 (pr1 (pr2 X)) x y)

  unit-law-mul-Monoid-Action :
    (x : type-Monoid-Action) → Id (mul-Monoid-Action (unit-Monoid M) x) x
  unit-law-mul-Monoid-Action = htpy-eq (pr2 (pr2 X))
```
