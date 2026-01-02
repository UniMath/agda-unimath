# Uniqueness of the image of a map

```agda
module foundation.uniqueness-image where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-slice
open import foundation.images
open import foundation.morphisms-slice
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
```

</details>

### Uniqueness of the image

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  where

  abstract
    is-equiv-is-image-is-image :
      is-image f i q →
      is-image f i' q' →
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h)
    is-equiv-is-image-is-image up-i up-i' =
      is-equiv-hom-slice-emb i i' h (map-inv-is-equiv (up-i' B i) q)

  abstract
    is-image-is-image-is-equiv :
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
      is-image f i q →
      is-image f i' q'
    is-image-is-image-is-equiv is-equiv-h up-i {l} =
      is-image-is-image' f i' q'
        ( λ C j r →
          comp-hom-slice
            ( map-emb i')
            ( map-emb i)
            ( map-emb j)
            ( map-inv-is-equiv (up-i C j) r)
            ( pair
              ( map-inv-is-equiv is-equiv-h)
              ( triangle-section
                ( map-emb i)
                ( map-emb i')
                ( map-hom-slice (map-emb i) (map-emb i') h)
                ( triangle-hom-slice (map-emb i) (map-emb i') h)
                ( pair
                  ( map-inv-is-equiv is-equiv-h)
                  ( is-section-map-inv-is-equiv is-equiv-h)))))

  abstract
    is-image-is-equiv-is-image :
      is-image f i' q' →
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
      is-image f i q
    is-image-is-equiv-is-image up-i' is-equiv-h {l} =
      is-image-is-image' f i q
        ( λ C j r →
          comp-hom-slice
            ( map-emb i)
            ( map-emb i')
            ( map-emb j)
            ( map-inv-is-equiv (up-i' C j) r)
            ( h))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (Hi : is-image f i q)
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (Hi' : is-image f i' q')
  where

  abstract
    uniqueness-image :
      is-contr
        ( Σ ( equiv-slice (map-emb i) (map-emb i'))
            ( λ e →
              htpy-hom-slice f
                ( map-emb i')
                ( comp-hom-slice f
                  ( map-emb i)
                  ( map-emb i')
                  ( hom-equiv-slice (map-emb i) (map-emb i') e)
                  ( q))
                ( q')))
    uniqueness-image =
      is-contr-equiv
        ( Σ ( Σ ( hom-slice (map-emb i) (map-emb i'))
                ( λ h →
                  htpy-hom-slice f
                    ( map-emb i')
                    ( comp-hom-slice f (map-emb i) (map-emb i') h q)
                    ( q')))
            ( λ h → is-equiv (pr1 (pr1 h))))
        ( ( equiv-right-swap-Σ) ∘e
          ( equiv-Σ
            ( λ h →
              htpy-hom-slice f
                ( map-emb i')
                ( comp-hom-slice f (map-emb i) (map-emb i') (pr1 h) q)
                ( q'))
            ( equiv-right-swap-Σ)
            ( λ ((e , E) , H) → id-equiv)))
        ( is-contr-equiv
          ( is-equiv
            ( map-hom-slice-universal-property-image f i q Hi i' q'))
          ( left-unit-law-Σ-is-contr
            ( universal-property-image f i q Hi i' q')
            ( center (universal-property-image f i q Hi i' q')))
          ( is-proof-irrelevant-is-prop
            ( is-property-is-equiv
              ( map-hom-slice-universal-property-image f i q Hi i' q'))
            ( is-equiv-is-image-is-image f i q i' q'
              ( hom-slice-universal-property-image f i q Hi i' q')
              ( Hi)
              ( Hi'))))

  equiv-slice-uniqueness-image : equiv-slice (map-emb i) (map-emb i')
  equiv-slice-uniqueness-image =
    pr1 (center uniqueness-image)

  hom-equiv-slice-uniqueness-image : hom-slice (map-emb i) (map-emb i')
  hom-equiv-slice-uniqueness-image =
    hom-equiv-slice (map-emb i) (map-emb i') (equiv-slice-uniqueness-image)

  map-hom-equiv-slice-uniqueness-image : B → B'
  map-hom-equiv-slice-uniqueness-image =
    map-hom-slice (map-emb i) (map-emb i') (hom-equiv-slice-uniqueness-image)

  abstract
    is-equiv-map-hom-equiv-slice-uniqueness-image :
      is-equiv map-hom-equiv-slice-uniqueness-image
    is-equiv-map-hom-equiv-slice-uniqueness-image =
      is-equiv-map-equiv (pr1 equiv-slice-uniqueness-image)

  equiv-equiv-slice-uniqueness-image : B ≃ B'
  pr1 equiv-equiv-slice-uniqueness-image = map-hom-equiv-slice-uniqueness-image
  pr2 equiv-equiv-slice-uniqueness-image =
    is-equiv-map-hom-equiv-slice-uniqueness-image

  triangle-hom-equiv-slice-uniqueness-image :
    (map-emb i) ~ (map-emb i' ∘ map-hom-equiv-slice-uniqueness-image)
  triangle-hom-equiv-slice-uniqueness-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb i')
      ( hom-equiv-slice-uniqueness-image)

  htpy-equiv-slice-uniqueness-image :
    htpy-hom-slice f
      ( map-emb i')
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb i')
        ( hom-equiv-slice-uniqueness-image)
        ( q))
      ( q')
  htpy-equiv-slice-uniqueness-image =
    pr2 (center uniqueness-image)

  htpy-map-hom-equiv-slice-uniqueness-image :
    ( map-hom-equiv-slice-uniqueness-image ∘ map-hom-slice f (map-emb i) q) ~
    ( map-hom-slice f (map-emb i') q')
  htpy-map-hom-equiv-slice-uniqueness-image =
    pr1 htpy-equiv-slice-uniqueness-image

  tetrahedron-hom-equiv-slice-uniqueness-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb i' ·l htpy-map-hom-equiv-slice-uniqueness-image)) ~
    ( triangle-hom-slice f (map-emb i') q')
  tetrahedron-hom-equiv-slice-uniqueness-image =
    pr2 htpy-equiv-slice-uniqueness-image
```

### Uniqueness of the image

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : is-image f i q)
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
