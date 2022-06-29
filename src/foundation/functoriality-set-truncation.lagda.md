---
title: Functoriality of set truncation
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.functoriality-set-truncation where

open import foundation.contractible-types using
  ( is-contr; center; eq-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.equivalences using
  ( map-inv-is-equiv; is-equiv; _≃_; map-equiv; is-equiv-map-equiv;
    is-equiv-htpy-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using (tot)
open import foundation.functoriality-truncation using
  ( unique-map-trunc; map-trunc; naturality-unit-trunc;
    htpy-uniqueness-map-trunc; id-map-trunc; comp-map-trunc;
    htpy-trunc; map-equiv-trunc; is-equiv-map-equiv-trunc; equiv-trunc)
open import foundation.homotopies using
  ( _~_; refl-htpy; _·l_; _∙h_; _·r_; inv-htpy)
open import foundation.identity-types using (_＝_; ap; _∙_; inv; refl)
open import foundation.images using
  ( im; inclusion-im; is-emb-inclusion-im; map-unit-im; triangle-unit-im;
    is-surjective-map-unit-im; unit-im; eq-Eq-im; im-Set)
open import foundation.injective-maps using
  ( is-injective; is-emb-is-injective; is-injective-is-emb)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (function-Prop)
open import foundation.set-truncations using
  ( type-trunc-Set; unit-trunc-Set; universal-property-trunc-Set; trunc-Set;
    dependent-universal-property-trunc-Set; map-equiv-trunc-Σ-Set;
    trunc-Σ-Set; equiv-trunc-Σ-Set; apply-effectiveness-unit-trunc-Set;
    apply-dependent-universal-property-trunc-Set'; is-surjective-unit-trunc-Set;
    is-set-type-trunc-Set; is-set-truncation-trunc-Set)
open import foundation.sets using (set-Prop; Id-Prop)
open import foundation.slice using
  ( hom-slice; equiv-slice; htpy-hom-slice; comp-hom-slice; hom-equiv-slice)
open import foundation.surjective-maps using (is-surjective)
open import foundation.truncation-levels using (zero-𝕋)
open import foundation.uniqueness-image using (uniqueness-im)
open import foundation.uniqueness-set-truncations using
  ( is-set-truncation-is-equiv-is-set-truncation)
open import foundation.universal-property-image using
  ( is-image; is-image-is-surjective)
open import foundation.universal-property-set-truncation using
  ( is-set-truncation)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of the set truncation implies that the set truncation acts functorially on maps between types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    unique-map-trunc-Set :
      is-contr
        ( Σ ( type-trunc-Set A → type-trunc-Set B)
            ( λ h → (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)))
    unique-map-trunc-Set = unique-map-trunc zero-𝕋 f

  map-trunc-Set :
    type-trunc-Set A → type-trunc-Set B
  map-trunc-Set = map-trunc zero-𝕋 f

  naturality-unit-trunc-Set :
    (map-trunc-Set ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)
  naturality-unit-trunc-Set = naturality-unit-trunc zero-𝕋 f

  htpy-uniqueness-map-trunc-Set :
    (h : type-trunc-Set A → type-trunc-Set B) →
    (H : (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)) →
    map-trunc-Set ~ h
  htpy-uniqueness-map-trunc-Set = htpy-uniqueness-map-trunc zero-𝕋 f
```

## Properties

### The functorial action of set truncations preserves identity maps

```agda
id-map-trunc-Set :
  {l1 : Level} {A : UU l1} → map-trunc-Set (id {A = A}) ~ id
id-map-trunc-Set = id-map-trunc zero-𝕋
```

### The functorial action of set truncations preserves composition

```agda
comp-map-trunc-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-trunc-Set (g ∘ f) ~ (map-trunc-Set g ∘ map-trunc-Set f)
comp-map-trunc-Set = comp-map-trunc zero-𝕋
```

### The functorial action of set truncations preserves homotopies

```
htpy-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-trunc-Set f ~ map-trunc-Set g)
htpy-trunc-Set = htpy-trunc
```

### The functorial action of set truncations preserves equivalences

```agda
map-equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Set A → type-trunc-Set B
map-equiv-trunc-Set = map-equiv-trunc zero-𝕋

is-equiv-map-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-equiv (map-equiv-trunc-Set e)
is-equiv-map-trunc-Set = is-equiv-map-equiv-trunc zero-𝕋

equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (type-trunc-Set A ≃ type-trunc-Set B)
equiv-trunc-Set = equiv-trunc zero-𝕋
```

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  square-trunc-Σ-Set :
    ( map-equiv-trunc-Σ-Set A B ∘ unit-trunc-Set) ~
    ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
  square-trunc-Σ-Set =
    pr2 (center (trunc-Σ-Set A B))

  htpy-map-equiv-trunc-Σ-Set :
    map-trunc-Set (tot (λ x → unit-trunc-Set)) ~ (map-equiv-trunc-Σ-Set A B)
  htpy-map-equiv-trunc-Σ-Set =
    htpy-uniqueness-map-trunc-Set
      ( tot (λ x → unit-trunc-Set))
      ( map-equiv-trunc-Σ-Set A B)
      ( square-trunc-Σ-Set)

  abstract
    is-equiv-map-trunc-tot-unit-trunc-Set :
      is-equiv (map-trunc-Set (tot (λ (x : A) → unit-trunc-Set {A = B x})))
    is-equiv-map-trunc-tot-unit-trunc-Set =
      is-equiv-htpy-equiv
        ( equiv-trunc-Σ-Set A B)
        ( htpy-map-equiv-trunc-Σ-Set)
```

### The set truncation functor preserves injective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-injective-map-trunc-Set :
      is-injective f → is-injective (map-trunc-Set f)
    is-injective-map-trunc-Set H {x} {y} =
      apply-dependent-universal-property-trunc-Set'
        ( λ u →
          set-Prop
            ( function-Prop (map-trunc-Set f u ＝ map-trunc-Set f y)
            ( Id-Prop (trunc-Set A) u y) ))
        ( λ a →
          apply-dependent-universal-property-trunc-Set'
          ( λ v →
            set-Prop
              ( function-Prop
                ( map-trunc-Set f (unit-trunc-Set a) ＝ map-trunc-Set f v)
                ( Id-Prop (trunc-Set A) (unit-trunc-Set a) v)))
          ( λ b p →
            apply-universal-property-trunc-Prop
              ( apply-effectiveness-unit-trunc-Set
                ( ( inv (naturality-unit-trunc-Set f a)) ∙
                  ( p ∙ (naturality-unit-trunc-Set f b))))
              ( Id-Prop (trunc-Set A) (unit-trunc-Set a) (unit-trunc-Set b))
              ( λ q → ap unit-trunc-Set (H q)))
          ( y))
        ( x)
```

### The set truncation functor preserves surjective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-surjective-map-trunc-Set :
      is-surjective f → is-surjective (map-trunc-Set f)
    is-surjective-map-trunc-Set H =
      apply-dependent-universal-property-trunc-Set'
        ( λ x → set-Prop (trunc-Prop (fib (map-trunc-Set f) x)))
        ( λ b →
          apply-universal-property-trunc-Prop
            ( H b)
            ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set b)))
            ( λ { (pair a p) →
                  unit-trunc-Prop
                    ( pair
                      ( unit-trunc-Set a)
                      ( naturality-unit-trunc-Set f a ∙ ap unit-trunc-Set p))}))
```

### If the set truncation of a map `f` is surjective, then `f` is surjective

```
  abstract
    is-surjective-is-surjective-map-trunc-Set :
      is-surjective (map-trunc-Set f) → is-surjective f
    is-surjective-is-surjective-map-trunc-Set H b =
      apply-universal-property-trunc-Prop
        ( H (unit-trunc-Set b))
        ( trunc-Prop (fib f b))
        ( λ { (pair x p) →
              apply-universal-property-trunc-Prop
                ( is-surjective-unit-trunc-Set A x)
                ( trunc-Prop (fib f b))
                ( λ { (pair a refl) →
                      apply-universal-property-trunc-Prop
                        ( apply-effectiveness-unit-trunc-Set
                          ( inv (naturality-unit-trunc-Set f a) ∙ p))
                        ( trunc-Prop (fib f b))
                        ( λ q → unit-trunc-Prop (pair a q))})})
```

### Set truncation preserves the image of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  inclusion-trunc-im-Set : type-trunc-Set (im f) → type-trunc-Set B
  inclusion-trunc-im-Set = map-trunc-Set (inclusion-im f)

  abstract
    is-emb-inclusion-trunc-im-Set : is-emb inclusion-trunc-im-Set
    is-emb-inclusion-trunc-im-Set =
      is-emb-is-injective
        ( is-set-type-trunc-Set)
        ( is-injective-map-trunc-Set
          ( inclusion-im f)
          ( is-injective-is-emb (is-emb-inclusion-im f)))

  emb-trunc-im-Set : type-trunc-Set (im f) ↪ type-trunc-Set B
  emb-trunc-im-Set = pair inclusion-trunc-im-Set is-emb-inclusion-trunc-im-Set

  abstract
    is-injective-inclusion-trunc-im-Set : is-injective inclusion-trunc-im-Set
    is-injective-inclusion-trunc-im-Set =
      is-injective-is-emb is-emb-inclusion-trunc-im-Set

  map-hom-slice-trunc-im-Set : type-trunc-Set A → type-trunc-Set (im f)
  map-hom-slice-trunc-im-Set = map-trunc-Set (map-unit-im f)

  triangle-hom-slice-trunc-im-Set :
    map-trunc-Set f ~ (inclusion-trunc-im-Set ∘ map-trunc-Set (map-unit-im f))
  triangle-hom-slice-trunc-im-Set =
    ( htpy-trunc-Set (triangle-unit-im f)) ∙h
    ( comp-map-trunc-Set (inclusion-im f) (map-unit-im f))

  hom-slice-trunc-im-Set : hom-slice (map-trunc-Set f) inclusion-trunc-im-Set
  hom-slice-trunc-im-Set =
    pair map-hom-slice-trunc-im-Set triangle-hom-slice-trunc-im-Set

  abstract
    is-surjective-map-hom-slice-trunc-im-Set :
      is-surjective map-hom-slice-trunc-im-Set
    is-surjective-map-hom-slice-trunc-im-Set =
      is-surjective-map-trunc-Set
        ( map-unit-im f)
        ( is-surjective-map-unit-im f)

  abstract
    is-image-trunc-im-Set :
      {l : Level} →
      is-image l
        ( map-trunc-Set f)
        ( emb-trunc-im-Set)
        ( hom-slice-trunc-im-Set)
    is-image-trunc-im-Set =
      is-image-is-surjective
        ( map-trunc-Set f)
        ( emb-trunc-im-Set)
        ( hom-slice-trunc-im-Set)
        ( is-surjective-map-hom-slice-trunc-im-Set)

  abstract
    unique-equiv-trunc-im-Set :
      is-contr
        ( Σ ( equiv-slice
              ( inclusion-im (map-trunc-Set f))
              ( inclusion-trunc-im-Set))
            ( λ e →
              htpy-hom-slice (map-trunc-Set f)
                ( inclusion-trunc-im-Set)
                ( comp-hom-slice (map-trunc-Set f)
                  ( inclusion-im (map-trunc-Set f))
                  ( inclusion-trunc-im-Set)
                  ( hom-equiv-slice
                    ( inclusion-im (map-trunc-Set f))
                    ( inclusion-trunc-im-Set)
                    ( e))
                  ( unit-im (map-trunc-Set f)))
                ( hom-slice-trunc-im-Set)))
    unique-equiv-trunc-im-Set =
      uniqueness-im
        ( map-trunc-Set f)
        ( emb-trunc-im-Set)
        ( hom-slice-trunc-im-Set)
        ( is-image-trunc-im-Set)

  equiv-slice-trunc-im-Set :
    equiv-slice (inclusion-im (map-trunc-Set f)) inclusion-trunc-im-Set
  equiv-slice-trunc-im-Set = pr1 (center unique-equiv-trunc-im-Set)

  equiv-trunc-im-Set : im (map-trunc-Set f) ≃ type-trunc-Set (im f)
  equiv-trunc-im-Set = pr1 equiv-slice-trunc-im-Set

  map-equiv-trunc-im-Set : im (map-trunc-Set f) → type-trunc-Set (im f)
  map-equiv-trunc-im-Set = map-equiv equiv-trunc-im-Set

  triangle-trunc-im-Set :
    ( inclusion-im (map-trunc-Set f)) ~
    ( inclusion-trunc-im-Set ∘ map-equiv-trunc-im-Set)
  triangle-trunc-im-Set = pr2 equiv-slice-trunc-im-Set

  htpy-hom-slice-trunc-im-Set :
    htpy-hom-slice
      ( map-trunc-Set f)
      ( inclusion-trunc-im-Set)
      ( comp-hom-slice
        ( map-trunc-Set f)
        ( inclusion-im (map-trunc-Set f))
        ( inclusion-trunc-im-Set)
        ( hom-equiv-slice
          ( inclusion-im (map-trunc-Set f))
          ( inclusion-trunc-im-Set)
          ( equiv-slice-trunc-im-Set))
        ( unit-im (map-trunc-Set f)))
      ( hom-slice-trunc-im-Set)
  htpy-hom-slice-trunc-im-Set =
    pr2 (center unique-equiv-trunc-im-Set)

  htpy-map-hom-slice-trunc-im-Set :
    ( map-equiv-trunc-im-Set ∘ (map-unit-im (map-trunc-Set f))) ~
    ( map-hom-slice-trunc-im-Set)
  htpy-map-hom-slice-trunc-im-Set =
    pr1 htpy-hom-slice-trunc-im-Set

  tetrahedron-map-hom-slice-trunc-im-Set :
    ( ( triangle-trunc-im-Set ·r map-unit-im (map-trunc-Set f)) ∙h
      ( inclusion-trunc-im-Set ·l htpy-map-hom-slice-trunc-im-Set)) ~
    ( triangle-hom-slice-trunc-im-Set)
  tetrahedron-map-hom-slice-trunc-im-Set =
    pr2 htpy-hom-slice-trunc-im-Set

  unit-im-map-trunc-Set :
    im f → im (map-trunc-Set f)
  unit-im-map-trunc-Set x =
    pair
      ( unit-trunc-Set (pr1 x))
      ( apply-universal-property-trunc-Prop (pr2 x)
        ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set (pr1 x))))
        ( λ u →
          unit-trunc-Prop
            ( pair
              ( unit-trunc-Set (pr1 u))
              ( naturality-unit-trunc-Set f (pr1 u) ∙ ap unit-trunc-Set (pr2 u)))))

  left-square-unit-im-map-trunc-Set :
    ( map-unit-im (map-trunc-Set f) ∘ unit-trunc-Set) ~
    ( unit-im-map-trunc-Set ∘ map-unit-im f)
  left-square-unit-im-map-trunc-Set a =
    eq-Eq-im
      ( map-trunc-Set f)
      ( map-unit-im (map-trunc-Set f) (unit-trunc-Set a))
      ( unit-im-map-trunc-Set (map-unit-im f a))
      ( naturality-unit-trunc-Set f a)

  right-square-unit-im-map-trunc-Set :
    ( inclusion-im (map-trunc-Set f) ∘ unit-im-map-trunc-Set) ~
    ( unit-trunc-Set ∘ inclusion-im f)
  right-square-unit-im-map-trunc-Set x = refl

  abstract
    is-set-truncation-im-map-trunc-Set :
      {l : Level} →
      is-set-truncation l
        ( im-Set (trunc-Set B) (map-trunc-Set f))
        ( unit-im-map-trunc-Set)
    is-set-truncation-im-map-trunc-Set =
      is-set-truncation-is-equiv-is-set-truncation
        ( im-Set (trunc-Set B) (map-trunc-Set f))
        ( unit-im-map-trunc-Set)
        ( trunc-Set (im f))
        ( unit-trunc-Set)
        ( λ b →
          is-injective-inclusion-trunc-im-Set
            ( ( inv (triangle-trunc-im-Set (unit-im-map-trunc-Set b))) ∙
              ( inv (naturality-unit-trunc-Set (inclusion-im f) b))))
        ( is-set-truncation-trunc-Set (im f))
        ( is-equiv-map-equiv equiv-trunc-im-Set)
```
