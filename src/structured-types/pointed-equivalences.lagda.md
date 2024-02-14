# Pointed equivalences

```agda
module structured-types.pointed-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-isomorphisms
open import structured-types.pointed-maps
open import structured-types.pointed-retractions
open import structured-types.pointed-sections
open import structured-types.pointed-types
open import structured-types.universal-property-pointed-equivalences
open import structured-types.whiskering-pointed-homotopies
```

</details>

## Idea

A {{#concept "pointed equivalence" Agda=_≃∗_}} is an equivalence in the category
of pointed spaces. Equivalently, a pointed equivalence is a
[pointed map](structured-types.pointed-maps.md) of which the underlying function
is an [equivalence](foundation-core.equivalences.md).

## Definitions

### Pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  is-pointed-equiv : (A →∗ B) → UU (l1 ⊔ l2)
  is-pointed-equiv f = is-equiv (map-pointed-map f)

  is-prop-is-pointed-equiv : (f : A →∗ B) → is-prop (is-pointed-equiv f)
  is-prop-is-pointed-equiv = is-property-is-equiv ∘ map-pointed-map

  is-pointed-equiv-Prop : (A →∗ B) → Prop (l1 ⊔ l2)
  is-pointed-equiv-Prop = is-equiv-Prop ∘ map-pointed-map

pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → UU (l1 ⊔ l2)
pointed-equiv A B =
  Σ ( type-Pointed-Type A ≃ type-Pointed-Type B)
    ( λ e → map-equiv e (point-Pointed-Type A) ＝ point-Pointed-Type B)

infix 6 _≃∗_

_≃∗_ = pointed-equiv

compute-pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ≃∗ B) ≃ Σ (A →∗ B) (is-pointed-equiv {A = A} {B})
compute-pointed-equiv A B = equiv-right-swap-Σ

inv-compute-pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Σ (A →∗ B) (is-pointed-equiv {A = A} {B}) ≃ (A ≃∗ B)
inv-compute-pointed-equiv A B = equiv-right-swap-Σ

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (e : A ≃∗ B)
  where

  equiv-pointed-equiv : type-Pointed-Type A ≃ type-Pointed-Type B
  equiv-pointed-equiv = pr1 e

  map-pointed-equiv : type-Pointed-Type A → type-Pointed-Type B
  map-pointed-equiv = map-equiv equiv-pointed-equiv

  is-equiv-map-pointed-equiv : is-equiv map-pointed-equiv
  is-equiv-map-pointed-equiv = is-equiv-map-equiv equiv-pointed-equiv

  preserves-point-pointed-equiv :
    Id (map-pointed-equiv (point-Pointed-Type A)) (point-Pointed-Type B)
  preserves-point-pointed-equiv = pr2 e

  pointed-map-pointed-equiv : A →∗ B
  pr1 pointed-map-pointed-equiv = map-pointed-equiv
  pr2 pointed-map-pointed-equiv = preserves-point-pointed-equiv

  is-pointed-equiv-pointed-equiv :
    is-pointed-equiv pointed-map-pointed-equiv
  is-pointed-equiv-pointed-equiv = is-equiv-map-pointed-equiv
```

### The identity pointed equivalence

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  id-pointed-equiv : A ≃∗ A
  pr1 id-pointed-equiv = id-equiv
  pr2 id-pointed-equiv = refl
```

### Composition of pointed equivalences

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  comp-pointed-equiv : (B ≃∗ C) → (A ≃∗ B) → (A ≃∗ C)
  pr1 (comp-pointed-equiv f e) =
    equiv-pointed-equiv f ∘e equiv-pointed-equiv e
  pr2 (comp-pointed-equiv f e) =
    preserves-point-comp-pointed-map
      ( pointed-map-pointed-equiv f)
      ( pointed-map-pointed-equiv e)
```

## Properties

### Extensionality of the universe of pointed types

```agda
module _
  {l1 : Level} (A : Pointed-Type l1)
  where

  is-torsorial-equiv-Pointed-Type :
    is-torsorial (λ B → A ≃∗ B)
  is-torsorial-equiv-Pointed-Type =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Pointed-Type A))
      ( type-Pointed-Type A , id-equiv)
      ( is-torsorial-Id (point-Pointed-Type A))

  extensionality-Pointed-Type : (B : Pointed-Type l1) → Id A B ≃ (A ≃∗ B)
  extensionality-Pointed-Type =
    extensionality-Σ
      ( λ b e → Id (map-equiv e (point-Pointed-Type A)) b)
      ( id-equiv)
      ( refl)
      ( λ B → equiv-univalence)
      ( λ a → id-equiv)

  eq-pointed-equiv : (B : Pointed-Type l1) → A ≃∗ B → Id A B
  eq-pointed-equiv B = map-inv-equiv (extensionality-Pointed-Type B)
```

### Being a pointed equivalence is equivalent to being a pointed isomorphism

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-contr-section-is-pointed-equiv :
    is-pointed-equiv f → is-contr (pointed-section f)
  is-contr-section-is-pointed-equiv H =
    is-torsorial-Eq-structure
      ( is-contr-section-is-equiv H)
      ( map-inv-is-equiv H , is-section-map-inv-is-equiv H)
      ( is-contr-map-is-equiv
        ( is-equiv-comp _ _
          ( is-emb-is-equiv H _ _)
          ( is-equiv-concat' _ (preserves-point-pointed-map f)))
        ( _))

  is-contr-retraction-is-pointed-equiv :
    is-pointed-equiv f → is-contr (pointed-retraction f)
  is-contr-retraction-is-pointed-equiv H =
    is-torsorial-Eq-structure
      ( is-contr-retraction-is-equiv H)
      ( map-inv-is-equiv H , is-retraction-map-inv-is-equiv H)
      ( is-contr-map-is-equiv
        ( is-equiv-concat _ _)
        ( _))

  is-contr-is-iso-is-pointed-equiv :
    is-pointed-equiv f → is-contr (is-pointed-iso f)
  is-contr-is-iso-is-pointed-equiv H =
    is-contr-product
      ( is-contr-section-is-pointed-equiv H)
      ( is-contr-retraction-is-pointed-equiv H)

  is-iso-is-pointed-equiv :
    is-pointed-equiv f → is-pointed-iso f
  is-iso-is-pointed-equiv H =
    center (is-contr-is-iso-is-pointed-equiv H)

  is-equiv-is-pointed-iso :
    is-pointed-iso f → is-pointed-equiv f
  pr1 (is-equiv-is-pointed-iso H) = section-is-pointed-iso H
  pr2 (is-equiv-is-pointed-iso H) = retraction-is-pointed-iso H

  is-prop-is-pointed-iso : is-prop (is-pointed-iso f)
  is-prop-is-pointed-iso =
    is-prop-is-proof-irrelevant
      ( λ H → is-contr-is-iso-is-pointed-equiv (is-equiv-is-pointed-iso H))

  equiv-is-iso-is-pointed-equiv :
    is-pointed-equiv f ≃ (is-pointed-iso f)
  pr1 equiv-is-iso-is-pointed-equiv = is-iso-is-pointed-equiv
  pr2 equiv-is-iso-is-pointed-equiv =
    is-equiv-is-prop
      ( is-property-is-equiv (map-pointed-map f))
      ( is-prop-is-pointed-iso)
      ( is-equiv-is-pointed-iso)
```

### Any pointed map satisfying the universal property of pointed equivalences is a pointed equivalence

In other words, any pointed map `f : A →∗ B` such that precomposing by `f`

```text
  - ∘∗ f : (B →∗ C) → (A →∗ C)
```

is an equivalence for any pointed type `C` is an equivalence.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (H : universal-property-pointed-equiv f)
  where

  pointed-map-inv-is-equiv-universal-property-pointed-equiv : B →∗ A
  pointed-map-inv-is-equiv-universal-property-pointed-equiv =
    map-inv-is-equiv (H A) (id-pointed-map)

  map-inv-is-equiv-universal-property-pointed-equiv :
    type-Pointed-Type B → type-Pointed-Type A
  map-inv-is-equiv-universal-property-pointed-equiv =
    map-pointed-map
      pointed-map-inv-is-equiv-universal-property-pointed-equiv

  preserves-point-map-inv-is-equiv-universal-property-pointed-equiv :
    map-inv-is-equiv-universal-property-pointed-equiv
      ( point-Pointed-Type B) ＝
    point-Pointed-Type A
  preserves-point-map-inv-is-equiv-universal-property-pointed-equiv =
    preserves-point-pointed-map
      pointed-map-inv-is-equiv-universal-property-pointed-equiv

  is-pointed-retraction-pointed-map-inv-is-equiv-universal-property-pointed-equiv :
    is-pointed-retraction f
      pointed-map-inv-is-equiv-universal-property-pointed-equiv
  is-pointed-retraction-pointed-map-inv-is-equiv-universal-property-pointed-equiv =
    pointed-htpy-eq _ _ (is-section-map-inv-is-equiv (H A) (id-pointed-map))

  is-retraction-map-inv-is-equiv-universal-property-pointed-equiv :
    is-retraction
      ( map-pointed-map f)
      ( map-inv-is-equiv-universal-property-pointed-equiv)
  is-retraction-map-inv-is-equiv-universal-property-pointed-equiv =
    htpy-pointed-htpy
      ( is-pointed-retraction-pointed-map-inv-is-equiv-universal-property-pointed-equiv)

  is-pointed-section-pointed-map-inv-is-equiv-universal-property-pointed-equiv :
    is-pointed-section f
      pointed-map-inv-is-equiv-universal-property-pointed-equiv
  is-pointed-section-pointed-map-inv-is-equiv-universal-property-pointed-equiv =
    pointed-htpy-eq _ _
      ( is-injective-is-equiv (H B)
        ( eq-pointed-htpy ((f ∘∗ _) ∘∗ f) (id-pointed-map ∘∗ f)
          ( concat-pointed-htpy
            ( associative-comp-pointed-map f _ f)
            ( concat-pointed-htpy
              ( left-whisker-pointed-htpy f _ _
                ( is-pointed-retraction-pointed-map-inv-is-equiv-universal-property-pointed-equiv))
              ( concat-pointed-htpy
                ( right-unit-law-comp-pointed-map f)
                ( inv-left-unit-law-comp-pointed-map f))))))

  is-section-map-inv-is-equiv-universal-property-pointed-equiv :
    is-section
      ( map-pointed-map f)
      ( map-inv-is-equiv-universal-property-pointed-equiv)
  is-section-map-inv-is-equiv-universal-property-pointed-equiv =
    htpy-pointed-htpy
      ( is-pointed-section-pointed-map-inv-is-equiv-universal-property-pointed-equiv)

  is-equiv-universal-property-pointed-equiv : is-pointed-equiv f
  is-equiv-universal-property-pointed-equiv =
    is-equiv-is-invertible
      ( map-inv-is-equiv-universal-property-pointed-equiv)
      ( is-section-map-inv-is-equiv-universal-property-pointed-equiv)
      ( is-retraction-map-inv-is-equiv-universal-property-pointed-equiv)
```

### Any pointed equivalence satisfies the universal property of pointed equivalences


```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  universal-property-pointed-equiv-is-pointed-equiv :
    is-pointed-equiv f →
    universal-property-pointed-equiv f
  universal-property-pointed-equiv-is-pointed-equiv E C = {!!}

{-
    pair
      ( pair
        ( precomp-pointed-map C h)
        ( λ k →
          eq-pointed-htpy
            ( (k ∘∗ h) ∘∗ f)
            ( k)
            ( concat-pointed-htpy
              ( (k ∘∗ h) ∘∗ f)
              ( k ∘∗ (h ∘∗ f))
              ( k)
              ( associative-comp-pointed-map k h f)
              ( concat-pointed-htpy
                ( k ∘∗ (h ∘∗ f))
                ( k ∘∗ id-pointed-map)
                ( k)
                ( left-whisker-pointed-htpy k
                  ( h ∘∗ f)
                  ( id-pointed-map)
                  ( H))
                ( right-unit-law-comp-pointed-map k)))))
      ( pair
        ( precomp-pointed-map C g)
        ( λ k →
          eq-pointed-htpy
            ( (k ∘∗ f) ∘∗ g)
            ( k)
            ( concat-pointed-htpy
              ( (k ∘∗ f) ∘∗ g)
              ( k ∘∗ (f ∘∗ g))
              ( k)
              ( associative-comp-pointed-map k f g)
              ( concat-pointed-htpy
                ( k ∘∗ (f ∘∗ g))
                ( k ∘∗ id-pointed-map)
                ( k)
                ( left-whisker-pointed-htpy k
                  ( f ∘∗ g)
                  ( id-pointed-map)
                  ( G))
                ( right-unit-law-comp-pointed-map k)))))
    where
    I : is-pointed-iso f
    I = is-iso-is-pointed-equiv f E
    g : B →∗ A
    g = pr1 (pr1 I)
    G : (f ∘∗ g) ~∗ id-pointed-map
    G = pr2 (pr1 I)
    h : B →∗ A
    h = pr1 (pr2 I)
    H : (h ∘∗ f) ~∗ id-pointed-map
    H = pr2 (pr2 I) -}

equiv-precomp-pointed-map :
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (C : Pointed-Type l3) → (A ≃∗ B) → (B →∗ C) ≃ (A →∗ C)
pr1 (equiv-precomp-pointed-map C f) g =
  g ∘∗ (pointed-map-pointed-equiv f)
pr2 (equiv-precomp-pointed-map C f) =
  universal-property-pointed-equiv-is-pointed-equiv
    ( pointed-map-pointed-equiv f)
    ( is-equiv-map-pointed-equiv f)
    ( C)
```

### Postcomposing by pointed equivalences is a pointed equivalence

```text
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-equiv-is-equiv-comp-pointed-map :
    ({l : Level} (X : Pointed-Type l) → is-equiv (comp-pointed-map {A = X} f)) →
    is-pointed-equiv f
  is-equiv-is-equiv-comp-pointed-map H = {!!}

{-
    is-equiv-is-invertible
      ( map-pointed-map g)
      ( pr1 G)
      ( htpy-eq
        ( ap pr1
          ( ap pr1
            ( eq-is-contr
              ( is-contr-map-is-equiv (H A) f)
                { pair
                  ( g ∘∗ f)
                  ( eq-pointed-htpy
                    ( f ∘∗ (g ∘∗ f))
                    ( f)
                    ( concat-pointed-htpy
                      ( f ∘∗ (g ∘∗ f))
                      ( (f ∘∗ g) ∘∗ f)
                      ( f)
                      ( inv-associative-comp-pointed-map f g f)
                      ( concat-pointed-htpy
                        ( (f ∘∗ g) ∘∗ f)
                        ( id-pointed-map ∘∗ f)
                        ( f)
                        ( right-whisker-pointed-htpy
                          ( f ∘∗ g)
                          ( id-pointed-map)
                          ( G)
                          ( f))
                        ( left-unit-law-comp-pointed-map f))))}
                { pair
                  ( id-pointed-map)
                  ( eq-pointed-htpy
                    ( f ∘∗ id-pointed-map)
                    ( f)
                    ( right-unit-law-comp-pointed-map f))}))))
    where
    g : B →∗ A
    g = pr1 (center (is-contr-map-is-equiv (H B) id-pointed-map))
    G : (f ∘∗ g) ~∗ id-pointed-map
    G = map-equiv
          ( extensionality-pointed-map
            ( f ∘∗ g)
            ( id-pointed-map))
        ( pr2 (center (is-contr-map-is-equiv (H B) id-pointed-map))) -}

  is-equiv-comp-is-pointed-equiv :
    is-pointed-equiv f →
    {l : Level} (X : Pointed-Type l) → is-equiv (comp-pointed-map {A = X} f)
  is-equiv-comp-is-pointed-equiv E X = {!!}

{-
    pair
      ( pair
        ( g ∘∗_)
        ( λ k →
          eq-pointed-htpy
            ( f ∘∗ (g ∘∗ k))
            ( k)
            ( concat-pointed-htpy
              ( f ∘∗ (g ∘∗ k))
              ( (f ∘∗ g) ∘∗ k)
              ( k)
              ( inv-associative-comp-pointed-map f g k)
              ( concat-pointed-htpy
                ( (f ∘∗ g) ∘∗ k)
                ( id-pointed-map ∘∗ k)
                ( k)
                ( right-whisker-pointed-htpy
                  ( f ∘∗ g)
                  ( id-pointed-map)
                  ( G)
                  ( k))
                ( left-unit-law-comp-pointed-map k)))))
      ( pair
        ( h ∘∗_)
        ( λ k →
          eq-pointed-htpy
            ( h ∘∗ (f ∘∗ k))
            ( k)
            ( concat-pointed-htpy
              ( h ∘∗ (f ∘∗ k))
              ( (h ∘∗ f) ∘∗ k)
              ( k)
              ( inv-associative-comp-pointed-map h f k)
              ( concat-pointed-htpy
                ( (h ∘∗ f) ∘∗ k)
                ( id-pointed-map ∘∗ k)
                ( k)
                ( right-whisker-pointed-htpy
                  ( h ∘∗ f)
                  ( id-pointed-map)
                  ( H)
                  ( k))
                ( left-unit-law-comp-pointed-map k)))))
    where
    I : is-pointed-iso f
    I = is-iso-is-pointed-equiv f E
    g : B →∗ A
    g = pr1 (pr1 I)
    G : (f ∘∗ g) ~∗ id-pointed-map
    G = pr2 (pr1 I)
    h : B →∗ A
    h = pr1 (pr2 I)
    H : (h ∘∗ f) ~∗ id-pointed-map
    H = pr2 (pr2 I) -}
```
