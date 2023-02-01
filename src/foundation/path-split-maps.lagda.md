---
title: Path-split maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.path-split-maps where

open import foundation-core.path-split-maps public

open import foundation-core.propositions
open import foundation-core.universe-levels

open import foundation.contractible-types
open import foundation.equivalences
```

## Properties

### Being path-split is a property

```agda
abstract
  is-prop-is-path-split :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-path-split f)
  is-prop-is-path-split f =
    is-prop-is-proof-irrelevant (λ is-path-split-f →
      let is-equiv-f = is-equiv-is-path-split f is-path-split-f in
      is-contr-prod
        ( is-contr-sec-is-equiv is-equiv-f)
        ( is-contr-Π
          ( λ x → is-contr-Π
            ( λ y → is-contr-sec-is-equiv (is-emb-is-equiv is-equiv-f x y)))))

abstract
  is-equiv-is-path-split-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-path-split-is-equiv f)
  is-equiv-is-path-split-is-equiv f =
    is-equiv-is-prop
      ( is-property-is-equiv f)
      ( is-prop-is-path-split f)
      ( is-equiv-is-path-split f)
```
