# The universal property of the image of a map

```agda
module foundation.universal-property-image where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.images
open import foundation.propositional-truncations
open import foundation.slice
open import foundation.surjective-maps
open import foundation.transport
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.logical-equivalences
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.subtypes
```

</details>

## Idea

The image of a map `f : A → X` is the least subtype of `X` containing all the
values of `f`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  where

  precomp-emb :
    {l4 : Level} {C : UU l4} ( j : C ↪ X) →
    hom-slice (map-emb i) (map-emb j) → hom-slice f (map-emb j)
  pr1 (precomp-emb j r) =
    ( map-hom-slice (map-emb i) (map-emb j) r) ∘
    ( map-hom-slice f (map-emb i) q)
  pr2 (precomp-emb j r) =
    ( triangle-hom-slice f (map-emb i) q) ∙h
    ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
      ( map-hom-slice f (map-emb i) q))

  is-image : UUω
  is-image = {l : Level} (C : UU l) (j : C ↪ X) → is-equiv (precomp-emb j)
```

### Simplified variant of `is-image`

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  where

  is-image' : UUω
  is-image' =
    {l : Level} (C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)
```

### The universal property of the image subtype

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  (B : subtype l3 X)
  where

  is-image-subtype : UUω
  is-image-subtype =
    {l : Level} (C : subtype l X) → (B ⊆ C) ↔ ((a : A) → is-in-subtype C (f a))
```

## Properties

### The two universal properties of the image of a map are equivalent

```agda
abstract
  is-image-is-image' :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-image' f i q → is-image f i q
  is-image-is-image' f i q up' C j =
    is-equiv-is-prop
      ( is-prop-hom-slice (map-emb i) j)
      ( is-prop-hom-slice f j)
      ( up' C j)

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : is-image f i q)
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

### The image subtype satisfies the universal property of the image subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  abstract
    forward-implication-is-image-subtype-subtype-im :
      {l : Level} (B : subtype l X) →
      subtype-im f ⊆ B → (a : A) → is-in-subtype B (f a)
    forward-implication-is-image-subtype-subtype-im B H a =
      H (f a) (unit-trunc-Prop (a , refl))

    backward-implication-is-image-subtype-subtype-im :
      {l : Level} (B : subtype l X) →
      ((a : A) → is-in-subtype B (f a)) → subtype-im f ⊆ B
    backward-implication-is-image-subtype-subtype-im B H x K =
      apply-universal-property-trunc-Prop K (B x) (λ {(a , refl) → H a})

    is-image-subtype-subtype-im : is-image-subtype f (subtype-im f)
    pr1 (is-image-subtype-subtype-im B) =
      forward-implication-is-image-subtype-subtype-im B
    pr2 (is-image-subtype-subtype-im B) =
      backward-implication-is-image-subtype-subtype-im B
```

### The identity embedding is the image inclusion of any map that has a section

```agda
abstract
  is-image-has-section :
    (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    section f → is-image f id-emb (pair f refl-htpy)
  is-image-has-section l f (pair g H) =
    is-image-is-image'
      f id-emb (pair f refl-htpy)
      ( λ B m h → pair ((pr1 h) ∘ g) ( λ x → (inv (H x)) ∙ (pr2 h (g x))))
```

### Any embedding is its own image inclusion

```agda
abstract
  is-image-is-emb :
    (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    (H : is-emb f) → is-image f (pair f H) (pair id refl-htpy)
  is-image-is-emb l f H =
    is-image-is-image'
      f (pair f H) (pair id refl-htpy)
      ( λ B m h → h)
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
        pair
          ( map-hom-slice f (map-emb m) h (pr1 t))
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
    is-image f (emb-im f) (unit-im f)
  is-image-im f {l} =
    is-image-is-image'
      f (emb-im f) (unit-im f)
      ( λ B m h →
        pair
          ( map-is-image-im f m h)
          ( triangle-is-image-im f m h))
```

### A factorization of a map through an embedding is the image factorization if and only if the right factor is surjective

```agda
abstract
  is-surjective-is-image :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-image f i q → is-surjective (map-hom-slice f (map-emb i) q)
  is-surjective-is-image {A = A} {B} {X} f i q up-i b =
    apply-universal-property-trunc-Prop β
      ( trunc-Prop (fib (map-hom-slice f (map-emb i) q) b))
      ( γ)
    where
    g : type-subtype (trunc-Prop ∘ fib (map-hom-slice f (map-emb i) q)) → X
    g = map-emb i ∘ pr1
    is-emb-g : is-emb g
    is-emb-g = is-emb-comp (map-emb i) pr1
      ( is-emb-map-emb i)
      ( is-emb-inclusion-subtype (λ x → trunc-Prop _))
    α : hom-slice (map-emb i) g
    α = map-inv-is-equiv
          ( up-i
            ( Σ B ( λ b →
                    type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)))
            ( pair g is-emb-g))
          ( pair (map-unit-im (pr1 q)) (pr2 q))
    β : type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)))
    β = pr2 (pr1 α b)
    γ :
      fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)) →
      type-Prop (trunc-Prop (fib (pr1 q) b))
    γ (pair a p) =
      unit-trunc-Prop
        ( pair a (p ∙ inv (is-injective-is-emb (is-emb-map-emb i) (pr2 α b))))

abstract
  is-image-is-surjective' :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-surjective (map-hom-slice f (map-emb i) q) →
    is-image' f i q
  is-image-is-surjective' f i q H B' m =
    map-equiv
      ( ( equiv-hom-slice-fiberwise-hom (map-emb i) (map-emb m)) ∘e
        ( ( inv-equiv (reduce-Π-fib (map-emb i) (fib (map-emb m)))) ∘e
          ( inv-equiv
            ( equiv-dependent-universal-property-surj-is-surjective
              ( pr1 q)
              ( H)
              ( λ b →
                pair
                  ( fib (map-emb m) (pr1 i b))
                  ( is-prop-map-emb m (pr1 i b)))) ∘e
            ( ( equiv-map-Π (λ a → equiv-tr (fib (map-emb m)) (pr2 q a))) ∘e
              ( ( reduce-Π-fib f (fib (map-emb m))) ∘e
                ( equiv-fiberwise-hom-hom-slice f (map-emb m)))))))

abstract
  is-image-is-surjective :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-surjective (map-hom-slice f (map-emb i) q) →
    is-image f i q
  is-image-is-surjective f i q H {l} =
    is-image-is-image' f i q
      ( is-image-is-surjective' f i q H)
```
