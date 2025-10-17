# Functoriality of set truncation

```agda
module foundation.functoriality-set-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-truncation
open import foundation.images
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.slice
open import foundation.surjective-maps
open import foundation.uniqueness-image
open import foundation.uniqueness-set-truncations
open import foundation.universal-property-image
open import foundation.universal-property-set-truncation
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Idea

The
[universal property of the set truncation](foundation.universal-property-set-truncation.md)
implies that the [set truncation](foundation.set-truncations.md) acts
functorially on maps between types.

## Definitions

### The functorial action of set-truncations on maps

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

  map-trunc-Set : type-trunc-Set A → type-trunc-Set B
  map-trunc-Set = map-trunc zero-𝕋 f

  naturality-unit-trunc-Set :
    map-trunc-Set ∘ unit-trunc-Set ~ unit-trunc-Set ∘ f
  naturality-unit-trunc-Set = naturality-unit-trunc zero-𝕋 f

  htpy-uniqueness-map-trunc-Set :
    (h : type-trunc-Set A → type-trunc-Set B) →
    (H : h ∘ unit-trunc-Set ~ unit-trunc-Set ∘ f) →
    map-trunc-Set ~ h
  htpy-uniqueness-map-trunc-Set = htpy-uniqueness-map-trunc zero-𝕋 f
```

### Functorial action of set-truncation on binary maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  binary-map-trunc-Set :
    type-trunc-Set A → type-trunc-Set B → type-trunc-Set C
  binary-map-trunc-Set x y =
    map-trunc-Set
      ( λ (x' , y') → f x' y')
      ( map-inv-equiv-distributive-trunc-product-Set A B (x , y))
```

## Properties

### The functorial action of set truncations preserves identity maps

```agda
id-map-trunc-Set : {l1 : Level} {A : UU l1} → map-trunc-Set (id {A = A}) ~ id
id-map-trunc-Set = id-map-trunc zero-𝕋
```

### The functorial action of set truncations preserves composition

```agda
preserves-comp-map-trunc-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-trunc-Set (g ∘ f) ~ (map-trunc-Set g ∘ map-trunc-Set f)
preserves-comp-map-trunc-Set = preserves-comp-map-trunc zero-𝕋
```

### The functorial action of set truncations preserves homotopies

```agda
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

### The set truncation functor preserves retracts

```agda
retract-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A retract-of B) → (type-trunc-Set A) retract-of (type-trunc-Set B)
retract-trunc-Set = retract-of-trunc-retract-of
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
            ( Id-Prop (trunc-Set A) u y)))
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
        ( λ x → set-Prop (trunc-Prop (fiber (map-trunc-Set f) x)))
        ( λ b →
          apply-universal-property-trunc-Prop
            ( H b)
            ( trunc-Prop (fiber (map-trunc-Set f) (unit-trunc-Set b)))
            ( λ (a , p) →
              unit-trunc-Prop
                ( ( unit-trunc-Set a) ,
                  ( naturality-unit-trunc-Set f a ∙ ap unit-trunc-Set p))))
```

### If the set truncation of a map `f` is surjective, then `f` is surjective

```agda
  abstract
    is-surjective-is-surjective-map-trunc-Set :
      is-surjective (map-trunc-Set f) → is-surjective f
    is-surjective-is-surjective-map-trunc-Set H b =
      apply-twice-universal-property-trunc-Prop'
        ( H (unit-trunc-Set b))
        ( λ (x , p) → is-surjective-unit-trunc-Set A x)
        ( trunc-Prop (fiber f b))
        ( λ where
          (x , p) ( a , refl) →
            map-trunc-Prop
              ( a ,_)
              ( apply-effectiveness-unit-trunc-Set
                ( inv (naturality-unit-trunc-Set f a) ∙ p)))
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
  pr1 emb-trunc-im-Set = inclusion-trunc-im-Set
  pr2 emb-trunc-im-Set = is-emb-inclusion-trunc-im-Set

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
    ( preserves-comp-map-trunc-Set (inclusion-im f) (map-unit-im f))

  hom-slice-trunc-im-Set : hom-slice (map-trunc-Set f) inclusion-trunc-im-Set
  pr1 hom-slice-trunc-im-Set = map-hom-slice-trunc-im-Set
  pr2 hom-slice-trunc-im-Set = triangle-hom-slice-trunc-im-Set

  abstract
    is-surjective-map-hom-slice-trunc-im-Set :
      is-surjective map-hom-slice-trunc-im-Set
    is-surjective-map-hom-slice-trunc-im-Set =
      is-surjective-map-trunc-Set
        ( map-unit-im f)
        ( is-surjective-map-unit-im f)

  abstract
    is-image-trunc-im-Set :
      is-image
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
  pr1 (unit-im-map-trunc-Set x) = unit-trunc-Set (pr1 x)
  pr2 (unit-im-map-trunc-Set x) =
    apply-universal-property-trunc-Prop (pr2 x)
      ( trunc-Prop (fiber (map-trunc-Set f) (unit-trunc-Set (pr1 x))))
      ( λ u →
        unit-trunc-Prop
          ( ( unit-trunc-Set (pr1 u)) ,
            ( naturality-unit-trunc-Set f (pr1 u) ∙
              ap unit-trunc-Set (pr2 u))))

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
      is-set-truncation
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
