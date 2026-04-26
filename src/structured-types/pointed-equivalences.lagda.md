# Pointed equivalences

```agda
module structured-types.pointed-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.path-algebra
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transposition-identifications-along-equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-retractions
open import structured-types.pointed-sections
open import structured-types.pointed-types
open import structured-types.postcomposition-pointed-maps
open import structured-types.precomposition-pointed-maps
open import structured-types.universal-property-pointed-equivalences
open import structured-types.whiskering-pointed-homotopies-composition
```

</details>

## Idea

A {{#concept "pointed equivalence" Agda=_≃∗_}} `e : A ≃∗ B` consists of an
[equivalence](foundation-core.equivalences.md) `e : A ≃ B` equipped with an
[identification](foundation-core.identity-types.md) `p : e * ＝ *` witnessing
that the underlying map of `e` preserves the base point of `A`.

The notion of pointed equivalence is described equivalently as a
[pointed map](structured-types.pointed-maps.md) of which the underlying function
is an [equivalence](foundation-core.equivalences.md), i.e.,

```text
  (A ≃∗ B) ≃ Σ (f : A →∗ B), is-equiv (map-pointed-map f)
```

Furthermore, a pointed equivalence can also be described equivalently as an
equivalence in the category of
[pointed types](structured-types.pointed-types.md).

## Definitions

### The predicate of being a pointed equivalence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-pointed-equiv : UU (l1 ⊔ l2)
  is-pointed-equiv = is-equiv (map-pointed-map f)

  is-prop-is-pointed-equiv : is-prop is-pointed-equiv
  is-prop-is-pointed-equiv = is-property-is-equiv (map-pointed-map f)

  is-pointed-equiv-Prop : Prop (l1 ⊔ l2)
  is-pointed-equiv-Prop = is-equiv-Prop (map-pointed-map f)

  module _
    (H : is-pointed-equiv)
    where

    map-inv-is-pointed-equiv : type-Pointed-Type B → type-Pointed-Type A
    map-inv-is-pointed-equiv = map-inv-is-equiv H

    is-section-map-inv-is-pointed-equiv :
      is-section (map-pointed-map f) map-inv-is-pointed-equiv
    is-section-map-inv-is-pointed-equiv = is-section-map-inv-is-equiv H

    is-retraction-map-inv-is-pointed-equiv :
      is-retraction (map-pointed-map f) map-inv-is-pointed-equiv
    is-retraction-map-inv-is-pointed-equiv =
      is-retraction-map-inv-is-equiv H

    preserves-point-map-inv-is-pointed-equiv :
      map-inv-is-pointed-equiv (point-Pointed-Type B) ＝ point-Pointed-Type A
    preserves-point-map-inv-is-pointed-equiv =
      preserves-point-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

    pointed-map-inv-is-pointed-equiv : B →∗ A
    pointed-map-inv-is-pointed-equiv =
      pointed-map-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

    coherence-point-is-retraction-map-inv-is-pointed-equiv :
      coherence-point-unpointed-htpy-pointed-Π
        ( pointed-map-inv-is-pointed-equiv ∘∗ f)
        ( id-pointed-map)
        ( is-retraction-map-inv-is-pointed-equiv)
    coherence-point-is-retraction-map-inv-is-pointed-equiv =
      coherence-point-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

    is-pointed-retraction-pointed-map-inv-is-pointed-equiv :
      is-pointed-retraction f pointed-map-inv-is-pointed-equiv
    is-pointed-retraction-pointed-map-inv-is-pointed-equiv =
      is-pointed-retraction-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

    coherence-point-is-section-map-inv-is-pointed-equiv :
      coherence-point-unpointed-htpy-pointed-Π
        ( f ∘∗ pointed-map-inv-is-pointed-equiv)
        ( id-pointed-map)
        ( is-section-map-inv-is-pointed-equiv)
    coherence-point-is-section-map-inv-is-pointed-equiv =
      ( right-whisker-concat
        ( ap-concat
          ( map-pointed-map f)
          ( inv (ap _ (preserves-point-pointed-map f)))
          ( _) ∙
          ( horizontal-concat-Id²
            ( ap-inv
              ( map-pointed-map f)
              ( ap _ (preserves-point-pointed-map f)) ∙
              ( inv
                ( ap
                  ( inv)
                  ( ap-comp
                    ( map-pointed-map f)
                    ( map-inv-is-pointed-equiv)
                    ( preserves-point-pointed-map f)))))
            ( inv (coherence-map-inv-is-equiv H (point-Pointed-Type A)))))
        ( preserves-point-pointed-map f)) ∙
      ( assoc
        ( inv
          ( ap
            ( map-pointed-map f ∘ map-inv-is-pointed-equiv)
            ( preserves-point-pointed-map f)))
        ( is-section-map-inv-is-pointed-equiv _)
        ( preserves-point-pointed-map f)) ∙
      ( inv
        ( ( right-unit) ∙
          ( left-transpose-eq-concat
            ( ap
              ( map-pointed-map f ∘ map-inv-is-pointed-equiv)
              ( preserves-point-pointed-map f))
            ( is-section-map-inv-is-pointed-equiv _)
            ( ( is-section-map-inv-is-pointed-equiv _) ∙
              ( preserves-point-pointed-map f))
            ( ( inv (nat-htpy is-section-map-inv-is-pointed-equiv _)) ∙
              ( left-whisker-concat
                ( is-section-map-inv-is-pointed-equiv _)
                ( ap-id (preserves-point-pointed-map f)))))))

    is-pointed-section-pointed-map-inv-is-pointed-equiv :
      is-pointed-section f pointed-map-inv-is-pointed-equiv
    pr1 is-pointed-section-pointed-map-inv-is-pointed-equiv =
      is-section-map-inv-is-pointed-equiv
    pr2 is-pointed-section-pointed-map-inv-is-pointed-equiv =
      coherence-point-is-section-map-inv-is-pointed-equiv
```

### Pointed equivalences

```agda
pointed-equiv :
  {l1 l2 : Level} → Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
pointed-equiv A B =
  Σ ( type-Pointed-Type A ≃ type-Pointed-Type B)
    ( λ e → map-equiv e (point-Pointed-Type A) ＝ point-Pointed-Type B)

infix 6 _≃∗_

_≃∗_ : {l1 l2 : Level} → Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
_≃∗_ = pointed-equiv

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (e : A ≃∗ B)
  where

  equiv-pointed-equiv : type-Pointed-Type A ≃ type-Pointed-Type B
  equiv-pointed-equiv = pr1 e

  map-pointed-equiv : type-Pointed-Type A → type-Pointed-Type B
  map-pointed-equiv = map-equiv equiv-pointed-equiv

  preserves-point-pointed-equiv :
    map-pointed-equiv (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-pointed-equiv = pr2 e

  pointed-map-pointed-equiv : A →∗ B
  pr1 pointed-map-pointed-equiv = map-pointed-equiv
  pr2 pointed-map-pointed-equiv = preserves-point-pointed-equiv

  is-equiv-map-pointed-equiv : is-equiv map-pointed-equiv
  is-equiv-map-pointed-equiv = is-equiv-map-equiv equiv-pointed-equiv

  is-pointed-equiv-pointed-equiv :
    is-pointed-equiv pointed-map-pointed-equiv
  is-pointed-equiv-pointed-equiv = is-equiv-map-pointed-equiv

  pointed-map-inv-pointed-equiv : B →∗ A
  pointed-map-inv-pointed-equiv =
    pointed-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  map-inv-pointed-equiv : type-Pointed-Type B → type-Pointed-Type A
  map-inv-pointed-equiv =
    map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  preserves-point-map-inv-pointed-equiv :
    map-inv-pointed-equiv (point-Pointed-Type B) ＝ point-Pointed-Type A
  preserves-point-map-inv-pointed-equiv =
    preserves-point-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  is-pointed-section-pointed-map-inv-pointed-equiv :
    is-pointed-section
      ( pointed-map-pointed-equiv)
      ( pointed-map-inv-pointed-equiv)
  is-pointed-section-pointed-map-inv-pointed-equiv =
    is-pointed-section-pointed-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  is-section-map-inv-pointed-equiv :
    is-section
      ( map-pointed-equiv)
      ( map-inv-pointed-equiv)
  is-section-map-inv-pointed-equiv =
    is-section-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  coherence-point-is-section-map-inv-pointed-equiv :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-pointed-equiv ∘∗ pointed-map-inv-pointed-equiv)
      ( id-pointed-map)
      ( is-section-map-inv-pointed-equiv)
  coherence-point-is-section-map-inv-pointed-equiv =
    coherence-point-is-section-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  is-pointed-retraction-pointed-map-inv-pointed-equiv :
    is-pointed-retraction
      ( pointed-map-pointed-equiv)
      ( pointed-map-inv-pointed-equiv)
  is-pointed-retraction-pointed-map-inv-pointed-equiv =
    is-pointed-retraction-pointed-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  is-retraction-map-inv-pointed-equiv :
    is-retraction
      ( map-pointed-equiv)
      ( map-inv-pointed-equiv)
  is-retraction-map-inv-pointed-equiv =
    is-retraction-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  coherence-point-is-retraction-map-inv-pointed-equiv :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-inv-pointed-equiv ∘∗ pointed-map-pointed-equiv)
      ( id-pointed-map)
      ( is-retraction-map-inv-pointed-equiv)
  coherence-point-is-retraction-map-inv-pointed-equiv =
    coherence-point-is-retraction-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)
```

### The equivalence between pointed equivalences and the type of pointed maps that are pointed equivalences

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  compute-pointed-equiv : (A ≃∗ B) ≃ Σ (A →∗ B) is-pointed-equiv
  compute-pointed-equiv = equiv-right-swap-Σ

  inv-compute-pointed-equiv : Σ (A →∗ B) is-pointed-equiv ≃ (A ≃∗ B)
  inv-compute-pointed-equiv = equiv-right-swap-Σ
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

### Inverses of pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  abstract
    is-pointed-equiv-inv-pointed-equiv :
      is-pointed-equiv (pointed-map-inv-pointed-equiv e)
    is-pointed-equiv-inv-pointed-equiv =
      is-equiv-is-invertible
        ( map-pointed-equiv e)
        ( is-retraction-map-inv-pointed-equiv e)
        ( is-section-map-inv-pointed-equiv e)

  equiv-inv-pointed-equiv : type-Pointed-Type B ≃ type-Pointed-Type A
  pr1 equiv-inv-pointed-equiv = map-inv-pointed-equiv e
  pr2 equiv-inv-pointed-equiv = is-pointed-equiv-inv-pointed-equiv

  inv-pointed-equiv : B ≃∗ A
  pr1 inv-pointed-equiv = equiv-inv-pointed-equiv
  pr2 inv-pointed-equiv = preserves-point-map-inv-pointed-equiv e
```

## Properties

### Extensionality of the universe of pointed types

```agda
module _
  {l1 : Level} (A : Pointed-Type l1)
  where

  abstract
    is-torsorial-pointed-equiv :
      is-torsorial (λ (B : Pointed-Type l1) → A ≃∗ B)
    is-torsorial-pointed-equiv =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (type-Pointed-Type A))
        ( type-Pointed-Type A , id-equiv)
        ( is-torsorial-Id (point-Pointed-Type A))

  extensionality-Pointed-Type : (B : Pointed-Type l1) → (A ＝ B) ≃ (A ≃∗ B)
  extensionality-Pointed-Type =
    extensionality-Σ
      ( λ b e → map-equiv e (point-Pointed-Type A) ＝ b)
      ( id-equiv)
      ( refl)
      ( λ B → equiv-univalence)
      ( λ a → id-equiv)

  eq-pointed-equiv : (B : Pointed-Type l1) → A ≃∗ B → A ＝ B
  eq-pointed-equiv B = map-inv-equiv (extensionality-Pointed-Type B)
```

### Any pointed map satisfying the universal property of pointed equivalences is a pointed equivalence

In other words, any pointed map `f : A →∗ B` such that precomposing by `f`

```text
  - ∘∗ f : (B →∗ C) → (A →∗ C)
```

is an equivalence for any pointed type `C`, is an equivalence.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (H : universal-property-pointed-equiv f)
  where

  pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv : B →∗ A
  pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv =
    map-inv-is-equiv (H A) id-pointed-map

  map-inv-is-pointed-equiv-universal-property-pointed-equiv :
    type-Pointed-Type B → type-Pointed-Type A
  map-inv-is-pointed-equiv-universal-property-pointed-equiv =
    map-pointed-map
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv

  preserves-point-map-inv-is-pointed-equiv-universal-property-pointed-equiv :
    map-inv-is-pointed-equiv-universal-property-pointed-equiv
      ( point-Pointed-Type B) ＝
    point-Pointed-Type A
  preserves-point-map-inv-is-pointed-equiv-universal-property-pointed-equiv =
    preserves-point-pointed-map
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv

  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv :
    is-pointed-retraction f
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv
  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv =
    pointed-htpy-eq _ _ (is-section-map-inv-is-equiv (H A) (id-pointed-map))

  is-retraction-map-inv-is-pointed-equiv-universal-property-pointed-equiv :
    is-retraction
      ( map-pointed-map f)
      ( map-inv-is-pointed-equiv-universal-property-pointed-equiv)
  is-retraction-map-inv-is-pointed-equiv-universal-property-pointed-equiv =
    htpy-pointed-htpy
      ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv)

  is-pointed-section-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv :
    is-pointed-section f
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv
  is-pointed-section-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv =
    pointed-htpy-eq _ _
      ( is-injective-is-equiv (H B)
        ( eq-pointed-htpy ((f ∘∗ _) ∘∗ f) (id-pointed-map ∘∗ f)
          ( concat-pointed-htpy
            ( associative-comp-pointed-map f _ f)
            ( concat-pointed-htpy
              ( left-whisker-comp-pointed-htpy f _ _
                ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv))
              ( concat-pointed-htpy
                ( right-unit-law-comp-pointed-map f)
                ( inv-left-unit-law-comp-pointed-map f))))))

  is-section-map-inv-is-pointed-equiv-universal-property-pointed-equiv :
    is-section
      ( map-pointed-map f)
      ( map-inv-is-pointed-equiv-universal-property-pointed-equiv)
  is-section-map-inv-is-pointed-equiv-universal-property-pointed-equiv =
    htpy-pointed-htpy
      ( is-pointed-section-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equiv)

  abstract
    is-pointed-equiv-universal-property-pointed-equiv : is-pointed-equiv f
    is-pointed-equiv-universal-property-pointed-equiv =
      is-equiv-is-invertible
        ( map-inv-is-pointed-equiv-universal-property-pointed-equiv)
        ( is-section-map-inv-is-pointed-equiv-universal-property-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv-universal-property-pointed-equiv)
```

### Any pointed equivalence satisfies the universal property of pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  map-inv-universal-property-pointed-equiv-is-pointed-equiv :
    (H : is-pointed-equiv f) {l : Level} (C : Pointed-Type l) →
    (A →∗ C) → (B →∗ C)
  map-inv-universal-property-pointed-equiv-is-pointed-equiv H C =
    precomp-pointed-map
      ( pointed-map-inv-is-pointed-equiv f H)
      ( C)

  is-section-map-inv-universal-property-pointed-equiv-is-pointed-equiv :
    (H : is-pointed-equiv f) →
    {l : Level} (C : Pointed-Type l) →
    is-section
      ( precomp-pointed-map f C)
      ( map-inv-universal-property-pointed-equiv-is-pointed-equiv
        ( H)
        ( C))
  is-section-map-inv-universal-property-pointed-equiv-is-pointed-equiv H C h =
    eq-pointed-htpy
      ( (h ∘∗ pointed-map-inv-is-pointed-equiv f H) ∘∗ f)
      ( h)
      ( concat-pointed-htpy
        ( associative-comp-pointed-map h
          ( pointed-map-inv-is-pointed-equiv f H)
          ( f))
        ( left-whisker-comp-pointed-htpy h
          ( pointed-map-inv-is-pointed-equiv f H ∘∗ f)
          ( id-pointed-map)
          ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv f H)))

  section-universal-property-pointed-equiv-is-pointed-equiv :
    (H : is-pointed-equiv f) →
    {l : Level} (C : Pointed-Type l) →
    section (precomp-pointed-map f C)
  pr1 (section-universal-property-pointed-equiv-is-pointed-equiv H C) =
    map-inv-universal-property-pointed-equiv-is-pointed-equiv H C
  pr2 (section-universal-property-pointed-equiv-is-pointed-equiv H C) =
    is-section-map-inv-universal-property-pointed-equiv-is-pointed-equiv
      ( H)
      ( C)

  is-retraction-map-inv-universal-property-pointed-equiv-is-pointed-equiv :
    (H : is-pointed-equiv f) →
    {l : Level} (C : Pointed-Type l) →
    is-retraction
      ( precomp-pointed-map f C)
      ( map-inv-universal-property-pointed-equiv-is-pointed-equiv
        ( H)
        ( C))
  is-retraction-map-inv-universal-property-pointed-equiv-is-pointed-equiv
    H C h =
    eq-pointed-htpy
      ( (h ∘∗ f) ∘∗ pointed-map-inv-is-pointed-equiv f H)
      ( h)
      ( concat-pointed-htpy
        ( associative-comp-pointed-map h f
          ( pointed-map-inv-is-pointed-equiv f H))
        ( left-whisker-comp-pointed-htpy h
          ( f ∘∗ pointed-map-inv-is-pointed-equiv f H)
          ( id-pointed-map)
          ( is-pointed-section-pointed-map-inv-is-pointed-equiv f H)))

  retraction-universal-property-pointed-equiv-is-pointed-equiv :
    (H : is-pointed-equiv f) →
    {l : Level} (C : Pointed-Type l) →
    retraction (precomp-pointed-map f C)
  pr1 (retraction-universal-property-pointed-equiv-is-pointed-equiv H C) =
    map-inv-universal-property-pointed-equiv-is-pointed-equiv H C
  pr2 (retraction-universal-property-pointed-equiv-is-pointed-equiv H C) =
    is-retraction-map-inv-universal-property-pointed-equiv-is-pointed-equiv
      ( H)
      ( C)

  abstract
    universal-property-pointed-equiv-is-pointed-equiv :
      is-pointed-equiv f →
      universal-property-pointed-equiv f
    pr1 (universal-property-pointed-equiv-is-pointed-equiv H C) =
      section-universal-property-pointed-equiv-is-pointed-equiv H C
    pr2 (universal-property-pointed-equiv-is-pointed-equiv H C) =
      retraction-universal-property-pointed-equiv-is-pointed-equiv H C

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

#### The predicate of being an equivalence by postcomposition of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-equiv-postcomp-pointed-map : UUω
  is-equiv-postcomp-pointed-map =
    {l : Level} (X : Pointed-Type l) → is-equiv (postcomp-pointed-map f X)
```

#### Any pointed map that is an equivalence by postcomposition is a pointed equivalence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (H : is-equiv-postcomp-pointed-map f)
  where

  pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map : B →∗ A
  pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map =
    map-inv-is-equiv (H B) id-pointed-map

  map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map :
    type-Pointed-Type B → type-Pointed-Type A
  map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map =
    map-pointed-map
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)

  is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map :
    is-pointed-section f
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
  is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map =
    pointed-htpy-eq
      ( f ∘∗ pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
      ( id-pointed-map)
      ( is-section-map-inv-is-equiv (H B) id-pointed-map)

  is-section-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map :
    is-section
      ( map-pointed-map f)
      ( map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
  is-section-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map =
    htpy-pointed-htpy
      ( is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)

  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map :
    is-pointed-retraction f
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map =
    pointed-htpy-eq
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map ∘∗ f)
      ( id-pointed-map)
      ( is-injective-is-equiv
        ( H A)
        ( eq-pointed-htpy
          ( ( f) ∘∗
            ( ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map) ∘∗
              ( f)))
          ( f ∘∗ id-pointed-map)
          ( concat-pointed-htpy
            ( inv-associative-comp-pointed-map f _ f)
            ( concat-pointed-htpy
              ( right-whisker-comp-pointed-htpy
                ( f ∘∗ _)
                ( id-pointed-map)
                ( is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
                ( f))
              ( concat-pointed-htpy
                ( left-unit-law-comp-pointed-map f)
                ( inv-pointed-htpy (right-unit-law-comp-pointed-map f)))))))

  is-retraction-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map :
    is-retraction
      ( map-pointed-map f)
      ( map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
  is-retraction-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map =
    htpy-pointed-htpy
      ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)

  abstract
    is-pointed-equiv-is-equiv-postcomp-pointed-map : is-pointed-equiv f
    is-pointed-equiv-is-equiv-postcomp-pointed-map =
      is-equiv-is-invertible
        ( map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
        ( is-section-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
        ( is-retraction-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-map)
```

#### Any pointed equivalence is an equivalence by postcomposition

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (H : is-pointed-equiv f)
  where

  map-inv-is-equiv-postcomp-is-pointed-equiv :
    {l : Level} (X : Pointed-Type l) → (X →∗ B) → (X →∗ A)
  map-inv-is-equiv-postcomp-is-pointed-equiv =
    postcomp-pointed-map (pointed-map-inv-is-pointed-equiv f H)

  is-section-map-inv-is-equiv-postcomp-is-pointed-equiv :
    {l : Level} (X : Pointed-Type l) →
    is-section
      ( postcomp-pointed-map f X)
      ( map-inv-is-equiv-postcomp-is-pointed-equiv X)
  is-section-map-inv-is-equiv-postcomp-is-pointed-equiv X h =
    eq-pointed-htpy
      ( f ∘∗ (pointed-map-inv-is-pointed-equiv f H ∘∗ h))
      ( h)
      ( concat-pointed-htpy
        ( inv-associative-comp-pointed-map f
          ( pointed-map-inv-is-pointed-equiv f H)
          ( h))
        ( concat-pointed-htpy
          ( right-whisker-comp-pointed-htpy
            ( f ∘∗ pointed-map-inv-is-pointed-equiv f H)
            ( id-pointed-map)
            ( is-pointed-section-pointed-map-inv-is-pointed-equiv f H)
            ( h))
          ( left-unit-law-comp-pointed-map h)))

  is-retraction-map-inv-is-equiv-postcomp-is-pointed-equiv :
    {l : Level} (X : Pointed-Type l) →
    is-retraction
      ( postcomp-pointed-map f X)
      ( map-inv-is-equiv-postcomp-is-pointed-equiv X)
  is-retraction-map-inv-is-equiv-postcomp-is-pointed-equiv X h =
    eq-pointed-htpy
      ( pointed-map-inv-is-pointed-equiv f H ∘∗ (f ∘∗ h))
      ( h)
      ( concat-pointed-htpy
        ( inv-associative-comp-pointed-map
          ( pointed-map-inv-is-pointed-equiv f H)
          ( f)
          ( h))
        ( concat-pointed-htpy
          ( right-whisker-comp-pointed-htpy
            ( pointed-map-inv-is-pointed-equiv f H ∘∗ f)
            ( id-pointed-map)
            ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv f H)
            ( h))
          ( left-unit-law-comp-pointed-map h)))

  abstract
    is-equiv-postcomp-is-pointed-equiv : is-equiv-postcomp-pointed-map f
    is-equiv-postcomp-is-pointed-equiv X =
      is-equiv-is-invertible
        ( map-inv-is-equiv-postcomp-is-pointed-equiv X)
        ( is-section-map-inv-is-equiv-postcomp-is-pointed-equiv X)
        ( is-retraction-map-inv-is-equiv-postcomp-is-pointed-equiv X)

equiv-postcomp-pointed-map :
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (C : Pointed-Type l3) → (A ≃∗ B) → (C →∗ A) ≃ (C →∗ B)
pr1 (equiv-postcomp-pointed-map C e) =
  postcomp-pointed-map (pointed-map-pointed-equiv e) C
pr2 (equiv-postcomp-pointed-map C e) =
  is-equiv-postcomp-is-pointed-equiv
    ( pointed-map-pointed-equiv e)
    ( is-pointed-equiv-pointed-equiv e)
    ( C)
```

### The composition operation on pointed equivalences is a binary equivalence

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  abstract
    is-equiv-comp-pointed-equiv :
      (f : B ≃∗ C) → is-equiv (λ (e : A ≃∗ B) → comp-pointed-equiv f e)
    is-equiv-comp-pointed-equiv f =
      is-equiv-map-Σ _
        ( is-equiv-postcomp-equiv-equiv (equiv-pointed-equiv f))
        ( λ e →
          is-equiv-comp _
            ( ap (map-pointed-equiv f))
            ( is-emb-is-equiv (is-equiv-map-pointed-equiv f) _ _)
            ( is-equiv-concat' _ (preserves-point-pointed-equiv f)))

  equiv-comp-pointed-equiv : (f : B ≃∗ C) → (A ≃∗ B) ≃ (A ≃∗ C)
  pr1 (equiv-comp-pointed-equiv f) = comp-pointed-equiv f
  pr2 (equiv-comp-pointed-equiv f) = is-equiv-comp-pointed-equiv f

  abstract
    is-equiv-comp-pointed-equiv' :
      (e : A ≃∗ B) → is-equiv (λ (f : B ≃∗ C) → comp-pointed-equiv f e)
    is-equiv-comp-pointed-equiv' e =
      is-equiv-map-Σ _
        ( is-equiv-precomp-equiv-equiv (equiv-pointed-equiv e))
        ( λ f →
          is-equiv-concat
            ( ap (map-equiv f) (preserves-point-pointed-equiv e))
            ( _))

  equiv-comp-pointed-equiv' :
    (e : A ≃∗ B) → (B ≃∗ C) ≃ (A ≃∗ C)
  pr1 (equiv-comp-pointed-equiv' e) f = comp-pointed-equiv f e
  pr2 (equiv-comp-pointed-equiv' e) = is-equiv-comp-pointed-equiv' e

  abstract
    is-binary-equiv-comp-pointed-equiv :
      is-binary-equiv (λ (f : B ≃∗ C) (e : A ≃∗ B) → comp-pointed-equiv f e)
    pr1 is-binary-equiv-comp-pointed-equiv = is-equiv-comp-pointed-equiv'
    pr2 is-binary-equiv-comp-pointed-equiv = is-equiv-comp-pointed-equiv
```
