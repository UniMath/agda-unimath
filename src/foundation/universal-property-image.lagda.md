---
title: The universal property of the image of a map
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-image where

open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; center; is-contr-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using
  ( _↪_; map-emb; id-emb; is-emb; is-emb-comp'; is-emb-map-emb)
open import foundation.equivalences using
  ( is-equiv; map-inv-is-equiv; triangle-section; issec-map-inv-is-equiv; _∘e_;
    id-equiv; is-property-is-equiv; is-equiv-map-equiv; _≃_; map-equiv;
    inv-equiv)
open import foundation.fibers-of-maps using (fib; reduce-Π-fib)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-function-types using
  ( equiv-map-Π)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot; equiv-Σ)
open import foundation.homotopies using (_∙h_; _·r_; _~_; _·l_; refl-htpy)
open import foundation.identity-types using (inv; _∙_; equiv-tr)
open import foundation.images using
  ( im; inclusion-im; emb-im; unit-im; map-unit-im)
open import foundation.injective-maps using (is-injective-is-emb)
open import foundation.propositional-maps using (fib-emb-Prop; is-prop-map-emb)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; is-prop-type-trunc-Prop; map-universal-property-trunc-Prop;
    trunc-Prop; unit-trunc-Prop; apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( is-equiv-is-prop; is-proof-irrelevant-is-prop; type-Prop)
open import foundation.sections using (sec)
open import foundation.slice using
  ( hom-slice; map-hom-slice; triangle-hom-slice; is-prop-hom-slice;
    htpy-hom-slice; comp-hom-slice; extensionality-hom-slice;
    is-equiv-hom-slice-emb; equiv-slice; hom-equiv-slice;
    equiv-hom-slice-fiberwise-hom; equiv-fiberwise-hom-hom-slice)
open import foundation.subtypes using
  ( type-subtype; is-emb-inclusion-subtype; eq-subtype)
open import foundation.surjective-maps using
  ( is-surjective; equiv-dependent-universal-property-surj-is-surjective)
open import foundation.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr; equiv-right-swap-Σ)
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

### A factorization of a map through an embedding is the image factorization if and only if the right factor is surjective

```agda
abstract
  is-surjective-is-image :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    ({l : Level} → is-image l f i q) →
    is-surjective (map-hom-slice f (map-emb i) q)
  is-surjective-is-image {A = A} {B} {X} f i q up-i b =
    apply-universal-property-trunc-Prop β
      ( trunc-Prop (fib (map-hom-slice f (map-emb i) q) b))
      ( γ)
    where
    g : type-subtype
          ( λ b → trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)) →
        X
    g = map-emb i ∘ pr1
    is-emb-g : is-emb g
    is-emb-g = is-emb-comp' (map-emb i) pr1
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
    γ : fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)) →
        type-Prop (trunc-Prop (fib (pr1 q) b))
    γ (pair a p) =
      unit-trunc-Prop
        ( pair a (p ∙ inv (is-injective-is-emb (is-emb-map-emb i) (pr2 α b))))

abstract
  is-image-is-surjective' :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-surjective (map-hom-slice f (map-emb i) q) →
    ({l : Level} → is-image' l f i q)
  is-image-is-surjective' f i q H B' m =
    map-equiv
      ( ( equiv-hom-slice-fiberwise-hom (map-emb i) (map-emb m)) ∘e
        ( ( inv-equiv (reduce-Π-fib (map-emb i) (fib (map-emb m)))) ∘e
          ( inv-equiv
            ( equiv-dependent-universal-property-surj-is-surjective
              ( pr1 q)
              ( H)
              ( λ b →
                pair ( fib (map-emb m) (pr1 i b))
                     ( is-prop-map-emb m (pr1 i b)))) ∘e
            ( ( equiv-map-Π (λ a → equiv-tr (fib (map-emb m)) (pr2 q a))) ∘e
              ( ( reduce-Π-fib f (fib (map-emb m))) ∘e
                ( equiv-fiberwise-hom-hom-slice f (map-emb m)))))))

abstract
  is-image-is-surjective :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-surjective (map-hom-slice f (map-emb i) q) →
    ({l : Level} → is-image l f i q)
  is-image-is-surjective f i q H {l} =
    is-image-is-image' l f i q
      ( is-image-is-surjective' f i q H)
```
