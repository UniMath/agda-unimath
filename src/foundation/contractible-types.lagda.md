# Contractible types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.contractible-types where

open import foundation-core.contractible-types public

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-cartesian-product-types using (eq-pair)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( is-equiv; is-equiv-comp'; _≃_; map-inv-is-equiv;
    is-equiv-map-inv-is-equiv; is-equiv-has-inverse; isretr-map-inv-is-equiv)
open import foundation.function-extensionality using (funext)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using
  ( Id; refl; inv; _∙_; left-inv; ap; tr; eq-transpose-tr)
open import foundation.retractions using (_retract-of_)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Properties

### Contractible types are propositions

```agda
is-prop-is-contr :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → is-contr (Id x y)
pr1 (is-prop-is-contr H x y) = eq-is-contr H
pr2 (is-prop-is-contr H x .x) refl = left-inv (pr2 H x)
```

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
