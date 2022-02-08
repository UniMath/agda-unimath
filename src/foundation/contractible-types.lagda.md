# Contractible types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.contractible-types where

open import foundation-core.contractible-types public

open import foundation-core.contractible-maps using
  ( is-contr-map-is-equiv)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( map-inv-is-equiv; _≃_; is-equiv; is-equiv-has-inverse)
open import foundation-core.functions using (id)
open import foundation-core.functoriality-dependent-pair-types using (tot)
open import foundation-core.identity-types using (Id; left-inv; refl; ap)
open import foundation-core.singleton-induction using
  ( ind-singleton-is-contr; comp-singleton-is-contr)
open import foundation-core.truncated-types using
  ( is-trunc; is-trunc-succ-is-trunc)
open import foundation-core.truncation-levels using (𝕋; neg-two-𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_; lsuc)

open import foundation.constant-maps using (const)
open import foundation.function-extensionality using
  ( funext; htpy-eq; eq-htpy)
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

### Equivalent characterizations of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  ev-point : {l2 : Level} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
  ev-point a f = f a

  ev-point' : {l2 : Level} (a : A) {X : UU l2} → (A → X) → X
  ev-point' a f = f a

  dependent-universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-contr l a =
    (P : A → UU l) → is-equiv (ev-point a {P})

  universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  universal-property-contr l a =
    (X : UU l) → is-equiv (ev-point' a {X})

  universal-property-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) →
    ({l : Level} → universal-property-contr l a)
  universal-property-dependent-universal-property-contr a dup-contr {l} X =
    dup-contr {l} (λ x → X)

  abstract
    is-equiv-ev-point-universal-property-contr :
      (a : A) → ({l : Level} → universal-property-contr l a) →
      is-equiv (ev-point' a {A})
    is-equiv-ev-point-universal-property-contr a up-contr =
      up-contr A

  abstract
    is-contr-is-equiv-ev-point :
      (a : A) → is-equiv (ev-point' a {X = A}) → is-contr A
    pr1 (is-contr-is-equiv-ev-point a H) = a
    pr2 (is-contr-is-equiv-ev-point a H) =
      htpy-eq
        ( ap
          ( pr1)
          ( eq-is-contr'
            ( is-contr-map-is-equiv H a)
            ( pair (λ x → a) refl)
            ( pair id refl)))

  abstract
    is-contr-universal-property-contr :
      (a : A) →
      ({l : Level} → universal-property-contr l a) → is-contr A
    is-contr-universal-property-contr a up-contr =
      is-contr-is-equiv-ev-point a
        ( is-equiv-ev-point-universal-property-contr a up-contr)

  abstract
    is-contr-dependent-universal-property-contr :
      (a : A) →
      ({l : Level} → dependent-universal-property-contr l a) → is-contr A
    is-contr-dependent-universal-property-contr a dup-contr =
      is-contr-universal-property-contr a
        ( universal-property-dependent-universal-property-contr a dup-contr)

  abstract
    dependent-universal-property-contr-is-contr :
      (a : A) → is-contr A →
      {l : Level} → dependent-universal-property-contr l a
    dependent-universal-property-contr-is-contr a H {l} P =
      is-equiv-has-inverse
        ( ind-singleton-is-contr a H P)
        ( comp-singleton-is-contr a H P)
        ( λ f →
          eq-htpy
            ( ind-singleton-is-contr a H
              ( λ x → Id (ind-singleton-is-contr a H P (f a) x) (f x))
              ( comp-singleton-is-contr a H P (f a))))

  abstract
    universal-property-contr-is-contr :
      (a : A) → is-contr A → {l : Level} → universal-property-contr l a
    universal-property-contr-is-contr a H =
      universal-property-dependent-universal-property-contr a
        ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr a H X) = ev-point' a
  pr2 (equiv-universal-property-contr a H X) =
    universal-property-contr-is-contr a H X

  abstract
    is-equiv-self-diagonal-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) →
      is-equiv (λ x → const A A x)
    is-equiv-self-diagonal-is-equiv-diagonal H = H A

  abstract
    is-contr-is-equiv-self-diagonal :
      is-equiv (λ x → const A A x) → is-contr A
    is-contr-is-equiv-self-diagonal H =
      tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  abstract
    is-contr-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) → is-contr A
    is-contr-is-equiv-diagonal H =
      is-contr-is-equiv-self-diagonal
        ( is-equiv-self-diagonal-is-equiv-diagonal H)

  abstract
    is-equiv-diagonal-is-contr :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (λ x → const A X x)
    is-equiv-diagonal-is-contr H X =
      is-equiv-has-inverse
        ( ev-point' (center H))
        ( λ f → eq-htpy (λ x → ap f (contraction H x)))
        ( λ x → refl)

  equiv-diagonal-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-is-contr X H) = const A X
  pr2 (equiv-diagonal-is-contr X H) = is-equiv-diagonal-is-contr H X
```
