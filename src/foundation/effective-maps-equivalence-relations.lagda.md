# Effective maps for equivalence relations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.effective-maps-equivalence-relations where

open import foundation.cartesian-product-types using (_×_)
open import foundation.equivalence-relations using (Eq-Rel; sim-Eq-Rel)
open import foundation.equivalences using (_≃_)
open import foundation.identity-types using (Id)
open import foundation.surjective-maps using (is-surjective)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Consider a type `A` equipped with an equivalence relation `R`, and let `f : A → X` be a map. Then `f` is effective if `R x y ≃ Id (f x) (f y)` for all `x y : A`. If `f` is both effective and surjective, then it follows that `X` satisfies the universal property of the quotient `A/R`.

## Definition

### Effective maps

```agda
is-effective :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
is-effective {A = A} R f =
  (x y : A) → Id (f x) (f y) ≃ sim-Eq-Rel R x y
```

### Maps that are effective and surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-surjective-and-effective :
    {l3 : Level} {B : UU l3} (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
  is-surjective-and-effective f = is-surjective f × is-effective R f
```
