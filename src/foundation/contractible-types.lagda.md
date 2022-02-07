# Contractible types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.contractible-types where

open import foundation-core.contractible-types public

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using (map-inv-is-equiv; _≃_)
open import foundation-core.identity-types using (Id; left-inv; refl)
open import foundation-core.truncated-types using
  ( is-trunc; is-trunc-succ-is-trunc)
open import foundation-core.truncation-levels using (𝕋; neg-two-𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.function-extensionality using (funext)
```

## Properties

### Products of families of contractible types are contractible

```agda
abstract
  is-contr-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  pr1 (is-contr-Π {A = A} {B = B} H) x = center (H x)
  pr2 (is-contr-Π {A = A} {B = B} H) f =
    map-inv-is-equiv
      ( funext (λ x → center (H x)) f)
      ( λ x → contraction (H x) (f x))
```

### The type of equivalences between contractible types is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-equiv-is-contr :
    is-contr A → is-contr B → is-contr (A ≃ B)
  is-contr-equiv-is-contr (pair a α) (pair b β) =
    is-contr-Σ
      ( is-contr-Π (λ x → (pair b β)))
      ( λ x → b)
      ( is-contr-prod
        ( is-contr-Σ
          ( is-contr-Π (λ y → (pair a α)))
          ( λ y → a)
          ( is-contr-Π (λ y → is-prop-is-contr (pair b β) b y)))
        ( is-contr-Σ
          ( is-contr-Π (λ x → pair a α))
          ( λ y → a)
          ( is-contr-Π (λ x → is-prop-is-contr (pair a α) a x))))
```

### Being contractible is a proposition

```agda
module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-contr-is-contr : is-contr A → is-contr (is-contr A)
    is-contr-is-contr (pair a α) =
      is-contr-Σ
        ( pair a α)
        ( a)
        ( is-contr-Π (λ x → is-prop-is-contr (pair a α) a x))

  abstract
    is-subtype-is-contr : (H K : is-contr A) → is-contr (Id H K)
    is-subtype-is-contr H = is-prop-is-contr (is-contr-is-contr H) H

is-contr-Prop :
  {l : Level} → UU l → Σ (UU l) (λ X → (x y : X) → is-contr (Id x y))
pr1 (is-contr-Prop A) = is-contr A
pr2 (is-contr-Prop A) = is-subtype-is-contr
```

### Contractible types are k-truncated for any k.

```agda
module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-trunc-is-contr : (k : 𝕋) → is-contr A → is-trunc k A
    is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
    is-trunc-is-contr (succ-𝕋 k) is-contr-A =
      is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)
```
