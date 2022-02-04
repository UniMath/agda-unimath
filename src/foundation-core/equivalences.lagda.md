# Equivalences

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.equivalences where

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (Σ)
open import foundation-core.retractions using (retr)
open import foundation-core.sections using (sec)
open import foundation-core.universe-levels using (Level; UU; _⊔_)
```

## Idea

An equivalence is a map that has a section and a (separate) retraction. This may look odd: Why not say that an equivalence is a map that has a 2-sided inverse? The reason is that the latter requirement would put nontrivial structure on the map, whereas having the section and retraction separate yields a property. To quickly see this: if `f` is an equivalence, then it has up to homotopy only one section, and it has up to homotopy only one retraction. 

## Definition

### Equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-equiv : (A → B) → UU (l1 ⊔ l2)
  is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) is-equiv
```
