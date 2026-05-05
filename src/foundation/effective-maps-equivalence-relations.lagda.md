# Effective maps for equivalence relations

```agda
module foundation.effective-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

Consider a type `A` equipped with an equivalence relation `R`, and let
`f : A → X` be a map. Then `f` is effective if `R x y ≃ (f x ＝ f y)` for all
`x y : A`. If `f` is both effective and surjective, then it follows that `X`
satisfies the universal property of the quotient `A/R`.

## Definition

### Effective maps

```agda
is-effective :
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) {B : UU l3}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
is-effective {A = A} R f =
  (x y : A) → (f x ＝ f y) ≃ sim-equivalence-relation R x y
```

### Maps that are effective and surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-surjective-and-effective :
    {l3 : Level} {B : UU l3} (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
  is-surjective-and-effective f = is-surjective f × is-effective R f
```
