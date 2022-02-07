# Dependent pair types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.dependent-pair-types where

open import foundation-core.dependent-pair-types public

open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

When `B` is a family of types over `A`, then we can form the type of pairs `pair a b` consisting of an element `a : A` and an element `b : B a`. Such pairs are called dependent pairs, since the type of the second component depends on the first component. 

### Families on dependent pair types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  fam-Σ : ((x : A) → B x → UU l3) → Σ A B → UU l3
  fam-Σ C (pair x y) = C x y
```
