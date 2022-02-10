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
    map-universal-property-trunc-Prop)
open import foundation.propositions using (is-prop)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.slice using
  ( hom-slice; map-hom-slice; triangle-hom-slice; equiv-slice; htpy-hom-slice;
    comp-hom-slice; hom-equiv-slice)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.subtypes using (is-emb-pr1)
open import foundation.truncated-types using (is-trunc; is-trunc-emb)
open import foundation.truncation-levels using
  ( 𝕋; succ-𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋)
open import foundation.universal-property-image using
  ( is-image; is-image-is-image'; uniqueness-image)
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

### The image of `f` is the image of `f`

```agda
abstract
  fiberwise-map-is-image-im :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
    (m : B ↪ X) (h : hom-slice f (map-emb m)) →
    (x : X) → type-trunc-Prop (fib f x) → fib (map-emb m) x
  fiberwise-map-is-image-im f m h x =
    map-universal-property-trunc-Prop
      { A = (fib f x)}
      ( fib-emb-Prop m x)
      ( λ t →
        pair ( map-hom-slice f (map-emb m) h (pr1 t))
             ( ( inv (triangle-hom-slice f (map-emb m) h (pr1 t))) ∙
               ( pr2 t)))
  
  map-is-image-im :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
    (m : B ↪ X) (h : hom-slice f (map-emb m)) → im f → B
  map-is-image-im f m h (pair x t) =
    pr1 (fiberwise-map-is-image-im f m h x t)
  
  triangle-is-image-im :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
    (m : B ↪ X) (h : hom-slice f (map-emb m)) →
    inclusion-im f ~ ((map-emb m) ∘ (map-is-image-im f m h))
  triangle-is-image-im f m h (pair x t) =
    inv (pr2 (fiberwise-map-is-image-im f m h x t))
  
  is-image-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    {l : Level} → is-image l f (emb-im f) (unit-im f)
  is-image-im f {l} =
    is-image-is-image'
      l f (emb-im f) (unit-im f)
      ( λ B m h →
        pair ( map-is-image-im f m h)
             ( triangle-is-image-im f m h))
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

### Uniqueness of the image

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  where

  abstract
    uniqueness-im :
      is-contr
        ( Σ ( equiv-slice (inclusion-im f) (map-emb i))
            ( λ e →
              htpy-hom-slice f
                ( map-emb i)
                ( comp-hom-slice f
                  ( inclusion-im f)
                  ( map-emb i)
                  ( hom-equiv-slice (inclusion-im f) (map-emb i) e)
                  ( unit-im f))
                ( q)))
    uniqueness-im =
      uniqueness-image f (emb-im f) (unit-im f) (is-image-im f) i q H
  
  equiv-slice-uniqueness-im : equiv-slice (inclusion-im f) (map-emb i)
  equiv-slice-uniqueness-im =
    pr1 (center uniqueness-im)

  hom-equiv-slice-uniqueness-im : hom-slice (inclusion-im f) (map-emb i)
  hom-equiv-slice-uniqueness-im =
    hom-equiv-slice (inclusion-im f) (map-emb i) equiv-slice-uniqueness-im

  map-hom-equiv-slice-uniqueness-im : im f → B
  map-hom-equiv-slice-uniqueness-im =
    map-hom-slice (inclusion-im f) (map-emb i) hom-equiv-slice-uniqueness-im

  abstract
    is-equiv-map-hom-equiv-slice-uniqueness-im :
      is-equiv map-hom-equiv-slice-uniqueness-im
    is-equiv-map-hom-equiv-slice-uniqueness-im =
      is-equiv-map-equiv (pr1 equiv-slice-uniqueness-im)

  equiv-equiv-slice-uniqueness-im : im f ≃ B
  pr1 equiv-equiv-slice-uniqueness-im = map-hom-equiv-slice-uniqueness-im
  pr2 equiv-equiv-slice-uniqueness-im =
    is-equiv-map-hom-equiv-slice-uniqueness-im

  triangle-hom-equiv-slice-uniqueness-im :
    (inclusion-im f) ~ (map-emb i ∘ map-hom-equiv-slice-uniqueness-im)
  triangle-hom-equiv-slice-uniqueness-im =
    triangle-hom-slice
      ( inclusion-im f)
      ( map-emb i)
      ( hom-equiv-slice-uniqueness-im)

  htpy-equiv-slice-uniqueness-im :
    htpy-hom-slice f
      ( map-emb i)
      ( comp-hom-slice f
        ( inclusion-im f)
        ( map-emb i)
        ( hom-equiv-slice-uniqueness-im)
        ( unit-im f))
      ( q)
  htpy-equiv-slice-uniqueness-im =
    pr2 (center uniqueness-im)

  htpy-map-hom-equiv-slice-uniqueness-im :
    ( ( map-hom-equiv-slice-uniqueness-im) ∘
      ( map-hom-slice f (inclusion-im f) (unit-im f))) ~
    ( map-hom-slice f (map-emb i) q)
  htpy-map-hom-equiv-slice-uniqueness-im =
    pr1 htpy-equiv-slice-uniqueness-im

  tetrahedron-hom-equiv-slice-uniqueness-im :
    ( ( ( triangle-hom-slice f (inclusion-im f) (unit-im f)) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-im) ·r
          ( map-hom-slice f (inclusion-im f) (unit-im f)))) ∙h
      ( map-emb i ·l htpy-map-hom-equiv-slice-uniqueness-im)) ~
    ( triangle-hom-slice f (map-emb i) q)
  tetrahedron-hom-equiv-slice-uniqueness-im =
    pr2 htpy-equiv-slice-uniqueness-im
```
