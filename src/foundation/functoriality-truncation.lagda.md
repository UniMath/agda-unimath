# Functoriality of truncations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.functoriality-truncation where

open import foundation.contractible-types using
  ( is-contr; center; contraction)
open import foundation.dependent-pair-types using
  ( Σ; pr1; pr2; pair)
open import foundation.equivalences using
  ( _≃_; map-equiv; map-inv-equiv; isretr-map-inv-equiv;
    issec-map-inv-equiv)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using
  ( _~_; refl-htpy; _·l_; _∙h_; _·r_; inv-htpy)
open import foundation.identity-types using (ap)
open import foundation.truncation-levels using (𝕋)
open import foundation.truncations using
  ( type-trunc; unit-trunc; universal-property-trunc;
    trunc)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of truncations can be used to define the functorial action of truncations.

## Definition

```agda
abstract
  unique-functor-trunc :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) (f : A → B) →
    is-contr
      ( Σ ( type-trunc k A → type-trunc k B)
          ( λ h → (h ∘ unit-trunc) ~ (unit-trunc ∘ f)))
  unique-functor-trunc {l1} {l2} {A} {B} k f =
    universal-property-trunc k A (trunc k B) (unit-trunc ∘ f)

abstract
  functor-trunc :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) →
    (A → B) → type-trunc k A → type-trunc k B
  functor-trunc k f =
    pr1 (center (unique-functor-trunc k f))
```

## Properties

### Truncations of homotopic maps are homotopic

```agda
  htpy-functor-trunc :
    { l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) (f : A → B) →
    ( (functor-trunc k f) ∘ unit-trunc) ~ (unit-trunc ∘ f)
  htpy-functor-trunc k f =
    pr2 (center (unique-functor-trunc k f))

  htpy-uniqueness-functor-trunc :
    { l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) (f : A → B) →
    ( h : type-trunc k A → type-trunc k B) →
    ( ( h ∘ unit-trunc) ~ (unit-trunc ∘ f)) →
    (functor-trunc k f) ~ h
  htpy-uniqueness-functor-trunc k f h H =
    htpy-eq (ap pr1 (contraction (unique-functor-trunc k f) (pair h H)))

  htpy-trunc :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {k : 𝕋} {f g : A → B} →
    (f ~ g) → (functor-trunc k f ~ functor-trunc k g)
  htpy-trunc {k = k} {f} {g} H =
    htpy-uniqueness-functor-trunc
      ( k)
      ( f)
      ( functor-trunc k g)
      ( htpy-functor-trunc k g ∙h
        inv-htpy (unit-trunc ·l H))
```

### The truncation of the identity map is the identity map

```agda
abstract
  id-functor-trunc :
    { l1 : Level} {A : UU l1} (k : 𝕋) → functor-trunc k (id {A = A}) ~ id
  id-functor-trunc {l1} {A} k =
    htpy-uniqueness-functor-trunc k id id refl-htpy
```

### The truncation of a composite is the composite of the truncations

```agda
abstract
  comp-functor-trunc :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (k : 𝕋)
    ( g : B → C) (f : A → B) →
    ( functor-trunc k (g ∘ f)) ~
    ( (functor-trunc k g) ∘ (functor-trunc k f))
  comp-functor-trunc k g f =
    htpy-uniqueness-functor-trunc k
      ( g ∘ f)
      ( (functor-trunc k g) ∘ (functor-trunc k f))
      ( ( (functor-trunc k g) ·l (htpy-functor-trunc k f)) ∙h
        ( ( htpy-functor-trunc k g) ·r f))
```

### Truncations of equivalences are equivalences

```agda
abstract
  map-equiv-trunc :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) →
    (A ≃ B) → type-trunc k A → type-trunc k B
  map-equiv-trunc k e = functor-trunc k (map-equiv e)

abstract
  map-inv-equiv-trunc :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) →
    (A ≃ B) → type-trunc k B → type-trunc k A
  map-inv-equiv-trunc k e = functor-trunc k (map-inv-equiv e)

abstract
  equiv-trunc :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) →
    (A ≃ B) → (type-trunc k A ≃ type-trunc k B)
  pr1 (equiv-trunc k e) = map-equiv-trunc k e
  pr2 (equiv-trunc k e) =
    pair
      ( pair
        ( map-inv-equiv-trunc k e)
        ( inv-htpy (comp-functor-trunc k (map-equiv e) (map-inv-equiv e)) ∙h
          ( htpy-trunc (issec-map-inv-equiv e) ∙h
            id-functor-trunc k)))
      ( pair
        ( map-inv-equiv-trunc k e)
        ( inv-htpy (comp-functor-trunc k (map-inv-equiv e) (map-equiv e)) ∙h
          ( htpy-trunc (isretr-map-inv-equiv e) ∙h
            id-functor-trunc k)))
```
