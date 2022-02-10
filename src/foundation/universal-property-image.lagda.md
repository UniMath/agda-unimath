# The universal property of the image of a map

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-image where

open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; center; is-contr-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_; map-emb; id-emb; is-emb)
open import foundation.equivalences using
  ( is-equiv; map-inv-is-equiv; triangle-section; issec-map-inv-is-equiv; _∘e_;
    id-equiv; is-subtype-is-equiv; is-equiv-map-equiv; _≃_)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot; equiv-Σ)
open import foundation.homotopies using (_∙h_; _·r_; _~_; _·l_; refl-htpy)
open import foundation.identity-types using (inv; _∙_)
open import foundation.propositions using
  ( is-equiv-is-prop; is-proof-irrelevant-is-prop)
open import foundation.sections using (sec)
open import foundation.slice using
  ( hom-slice; map-hom-slice; triangle-hom-slice; is-prop-hom-slice;
    htpy-hom-slice; comp-hom-slice; extensionality-hom-slice;
    is-equiv-hom-slice-emb; equiv-slice; hom-equiv-slice)
open import foundation.type-arithmetic-cartesian-product-types using
  ( equiv-right-swap-Σ)
open import foundation.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

The image of a map `f : A → X` is the least subtype of `X` containing all the values of `f`.

## Definition

```agda
precomp-emb :
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} ( i : B ↪ X) (q : hom-slice f (map-emb i)) →
  {C : UU l4} ( j : C ↪ X) →
  hom-slice (map-emb i) (map-emb j) → hom-slice f (map-emb j)
pr1 (precomp-emb f i q j r) =
  ( map-hom-slice (map-emb i) (map-emb j) r) ∘
  ( map-hom-slice f (map-emb i) q)
pr2 (precomp-emb f i q j r) =
  ( triangle-hom-slice f (map-emb i) q) ∙h
  ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
    ( map-hom-slice f (map-emb i) q))

is-image :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) → is-equiv (precomp-emb f i q j)
```

### Simplified variant of `is-image`

```agda
is-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image' l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)
```

## Properties

```agda
abstract
  is-image-is-image' :
    ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-image' l f i q → is-image l f i q
  is-image-is-image' l f i q up' C j =
    is-equiv-is-prop
      ( is-prop-hom-slice (map-emb i) j)
      ( is-prop-hom-slice f j)
      ( up' C j)

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  {C : UU l4} (j : C ↪ X) (r : hom-slice f (map-emb j))
  where

  abstract
    universal-property-image :
      is-contr
        ( Σ ( hom-slice (map-emb i) (map-emb j))
            ( λ h →
              htpy-hom-slice f
                ( map-emb j)
                ( comp-hom-slice f (map-emb i) (map-emb j) h q)
                ( r)))
    universal-property-image =
      is-contr-equiv'
        ( fib (precomp-emb f i q j) r)
        ( equiv-tot
          ( λ h →
            extensionality-hom-slice f (map-emb j) (precomp-emb f i q j h) r))
        ( is-contr-map-is-equiv (H C j) r)
                                      
  hom-slice-universal-property-image : hom-slice (map-emb i) (map-emb j)
  hom-slice-universal-property-image =
    pr1 (center universal-property-image)

  map-hom-slice-universal-property-image : B → C
  map-hom-slice-universal-property-image =
    map-hom-slice (map-emb i) (map-emb j) hom-slice-universal-property-image
  
  triangle-hom-slice-universal-property-image :
    (map-emb i) ~ (map-emb j ∘ map-hom-slice-universal-property-image)
  triangle-hom-slice-universal-property-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb j)
      ( hom-slice-universal-property-image)

  htpy-hom-slice-universal-property-image :
    htpy-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q))
      ( r)
  htpy-hom-slice-universal-property-image =
    pr2 (center universal-property-image)

  abstract
    htpy-map-hom-slice-universal-property-image :
      map-hom-slice f
        ( map-emb j)
        ( comp-hom-slice f
          ( map-emb i)
          ( map-emb j)
          ( hom-slice-universal-property-image)
          ( q)) ~
      map-hom-slice f (map-emb j) r
    htpy-map-hom-slice-universal-property-image =
      pr1 htpy-hom-slice-universal-property-image

    tetrahedron-hom-slice-universal-property-image :
      ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
          ( ( triangle-hom-slice-universal-property-image) ·r
            ( map-hom-slice f (map-emb i) q))) ∙h
        ( map-emb j ·l htpy-map-hom-slice-universal-property-image)) ~
      ( triangle-hom-slice f (map-emb j) r)
    tetrahedron-hom-slice-universal-property-image =
      pr2 htpy-hom-slice-universal-property-image
```

### Uniqueness of the image

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  -- (p : Id (comp-hom-slice f (map-emb i) (map-emb i') h q) q')
  where

  abstract
    is-equiv-is-image-is-image :
      ({l : Level} → is-image l f i q) →
      ({l : Level} → is-image l f i' q') →
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h)
    is-equiv-is-image-is-image up-i up-i' =
      is-equiv-hom-slice-emb i i' h (map-inv-is-equiv (up-i' B i) q)

  abstract
    is-image-is-image-is-equiv :
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
      ({l : Level} → is-image l f i q) →
      ({l : Level} → is-image l f i' q')
    is-image-is-image-is-equiv is-equiv-h up-i {l} =
      is-image-is-image' l f i' q'
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
                ( pair ( map-inv-is-equiv is-equiv-h)
                       ( issec-map-inv-is-equiv is-equiv-h)))))

  abstract
    is-image-is-equiv-is-image :
      ({l : Level} → is-image l f i' q') →
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
      ({l : Level} → is-image l f i q)
    is-image-is-equiv-is-image up-i' is-equiv-h {l} =
      is-image-is-image' l f i q
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
  (Hi : {l : Level} → is-image l f i q)
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (Hi' : {l : Level} → is-image l f i' q')
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
            ( λ { (pair (pair e E) H) → id-equiv})))
        ( is-contr-equiv
          ( is-equiv
            ( map-hom-slice-universal-property-image f i q Hi i' q'))
          ( left-unit-law-Σ-is-contr
            ( universal-property-image f i q Hi i' q')
            ( center (universal-property-image f i q Hi i' q')))
          ( is-proof-irrelevant-is-prop
            ( is-subtype-is-equiv
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

### The identity embedding is the image inclusion of any map that has a section

```agda
abstract
  is-image-has-section :
    (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    sec f → is-image l f id-emb (pair f refl-htpy)
  is-image-has-section l f (pair g H) =
    is-image-is-image'
      l f id-emb (pair f refl-htpy)
      ( λ B m h → pair ((pr1 h) ∘ g) ( λ x → (inv (H x)) ∙ (pr2 h (g x))))
```

### Any embedding is its own image inclusion

```agda
abstract
  is-image-is-emb :
    (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    (H : is-emb f) → is-image l f (pair f H) (pair id refl-htpy)
  is-image-is-emb l f H =
    is-image-is-image'
      l f (pair f H) (pair id refl-htpy)
      ( λ B m h → h)
```
