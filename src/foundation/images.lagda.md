# The image of a map

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.images where

open import foundation.1-types using
  ( is-1-type; UU-1-Type; type-1-Type; is-1-type-type-1-Type)
open import foundation.contractible-types using
  ( is-contr; is-contr-total-path; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using
  ( is-emb; _↪_; map-emb)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; is-equiv-map-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; _∙h_; _·r_; _·l_)
open import foundation.identity-types using (Id; refl; inv; _∙_)
open import foundation.injective-maps using (is-injective; is-injective-is-emb)
open import foundation.propositional-maps using (fib-emb-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; unit-trunc-Prop; is-prop-type-trunc-Prop;
    map-universal-property-trunc-Prop; trunc-Prop;
    apply-universal-property-trunc-Prop)
open import foundation.propositions using (is-prop; type-Prop)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.slice using
  ( hom-slice; map-hom-slice; triangle-hom-slice; equiv-slice; htpy-hom-slice;
    comp-hom-slice; hom-equiv-slice)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.subtypes using (is-emb-pr1; eq-subtype)
open import foundation.surjective-maps using (is-surjective)
open import foundation.truncated-types using (is-trunc; is-trunc-emb)
open import foundation.truncation-levels using
  ( 𝕋; succ-𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The image of a map is a type that satisfies the universal property of the image of a map.

## Definition

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where
    
  im : UU (l1 ⊔ l2)
  im = Σ X (λ x → type-trunc-Prop (fib f x))

  inclusion-im : im → X
  inclusion-im = pr1

  map-unit-im : A → im
  pr1 (map-unit-im a) = f a
  pr2 (map-unit-im a) = unit-trunc-Prop (pair a refl)

  triangle-unit-im : f ~ (inclusion-im ∘ map-unit-im)
  triangle-unit-im a = refl

  unit-im : hom-slice f inclusion-im
  pr1 unit-im = map-unit-im
  pr2 unit-im = triangle-unit-im
```

## Properties

### We characterize the identity type of im f

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  Eq-im : im f → im f → UU l1
  Eq-im x y = Id (pr1 x) (pr1 y)

  refl-Eq-im : (x : im f) → Eq-im x x
  refl-Eq-im x = refl

  Eq-eq-im : (x y : im f) → Id x y → Eq-im x y
  Eq-eq-im x .x refl = refl-Eq-im x

  abstract
    is-contr-total-Eq-im :
      (x : im f) → is-contr (Σ (im f) (Eq-im x))
    is-contr-total-Eq-im x =
      is-contr-total-Eq-subtype
        ( is-contr-total-path (pr1 x))
        ( λ x → is-prop-type-trunc-Prop)
        ( pr1 x)
        ( refl)
        ( pr2 x)

  abstract
    is-equiv-Eq-eq-im : (x y : im f) → is-equiv (Eq-eq-im x y)
    is-equiv-Eq-eq-im x =
      fundamental-theorem-id x
        ( refl-Eq-im x)
        ( is-contr-total-Eq-im x)
        ( Eq-eq-im x)

  equiv-Eq-eq-im : (x y : im f) → Id x y ≃ Eq-im x y
  pr1 (equiv-Eq-eq-im x y) = Eq-eq-im x y
  pr2 (equiv-Eq-eq-im x y) = is-equiv-Eq-eq-im x y

  eq-Eq-im : (x y : im f) → Eq-im x y → Id x y
  eq-Eq-im x y = map-inv-is-equiv (is-equiv-Eq-eq-im x y)
```

### The image inclusion is an embedding

```agda
abstract
  is-emb-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-emb (inclusion-im f)
  is-emb-inclusion-im f =
    is-emb-pr1 (λ x → is-prop-type-trunc-Prop)

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
pr1 (emb-im f) = inclusion-im f
pr2 (emb-im f) = is-emb-inclusion-im f
```

### The image inclusion is injective

```agda
abstract
  is-injective-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-injective (inclusion-im f)
  is-injective-inclusion-im f =
    is-injective-is-emb (is-emb-inclusion-im f)
```

### The unit map of the image is surjective

```agda
abstract
  is-surjective-map-unit-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-surjective (map-unit-im f)
  is-surjective-map-unit-im f (pair y z) =
    apply-universal-property-trunc-Prop z
      ( trunc-Prop (fib (map-unit-im f) (pair y z)))
      ( α)
    where
    α : fib f y → type-Prop (trunc-Prop (fib (map-unit-im f) (pair y z)))
    α (pair x p) =
      unit-trunc-Prop (pair x (eq-subtype (λ z → trunc-Prop (fib f z)) p))
```

### The image of a map into a truncated type is truncated

```agda
abstract
  is-trunc-im :
    {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
    is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im f)
  is-trunc-im k f = is-trunc-emb k (emb-im f) 
```

### The image of a map into a proposition is a proposition

```agda
abstract
  is-prop-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-prop X → is-prop (im f)
  is-prop-im = is-trunc-im neg-two-𝕋
```

### The image of a map into a set is a set

```agda
abstract
  is-set-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-set X → is-set (im f)
  is-set-im = is-trunc-im neg-one-𝕋

im-Set :
  {l1 l2 : Level} {A : UU l2} (X : UU-Set l1) (f : A → type-Set X) →
  UU-Set (l1 ⊔ l2)
pr1 (im-Set X f) = im f
pr2 (im-Set X f) = is-set-im f (is-set-type-Set X)
```

### The image of a map into a 1-type is a 1-type

```agda
abstract
  is-1-type-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-1-type X → is-1-type (im f)
  is-1-type-im = is-trunc-im zero-𝕋

im-1-Type :
  {l1 l2 : Level} {A : UU l2} (X : UU-1-Type l1)
  (f : A → type-1-Type X) → UU-1-Type (l1 ⊔ l2)
pr1 (im-1-Type X f) = im f
pr2 (im-1-Type X f) = is-1-type-im f (is-1-type-type-1-Type X)
```
