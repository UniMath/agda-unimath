# Set truncations

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.set-truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equality-coproduct-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.mere-equality
open import foundation.morphisms-slice
open import foundation.postcomposition-functions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.truncations
open import foundation.uniqueness-set-truncations
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universal-property-set-quotients
open import foundation.universal-property-set-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Idea

The {{#concept "set truncation" Agda=trunc-Set}} of a type `A` is a map
`η : A → trunc-Set A` that satisfies
[the universal property of set truncations](foundation.universal-property-set-truncation.md).

## Definitions

```agda
trunc-Set : {l : Level} → UU l → Set l
trunc-Set = trunc zero-𝕋

type-trunc-Set : {l : Level} → UU l → UU l
type-trunc-Set = type-trunc zero-𝕋

is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)
is-set-type-trunc-Set = is-trunc-type-trunc

unit-trunc-Set : {l : Level} {A : UU l} → A → type-trunc-Set A
unit-trunc-Set = unit-trunc

is-set-truncation-trunc-Set :
  {l1 : Level} (A : UU l1) → is-set-truncation (trunc-Set A) unit-trunc-Set
is-set-truncation-trunc-Set A = is-truncation-trunc

║_║₀ : {l : Level} → UU l → UU l
║_║₀ = type-trunc-Set
```

**Notation.** The [box drawings double vertical](https://codepoints.net/U+2551)
symbol `║` in the set truncation notation `║_║₀` can be inserted with
`agda-input` using the escape sequence `\--=` and selecting the second item in
the list.

## Properties

### The dependent universal property of set truncations

```agda
dependent-universal-property-trunc-Set :
  {l1 : Level} {A : UU l1} →
  dependent-universal-property-set-truncation (trunc-Set A) unit-trunc-Set
dependent-universal-property-trunc-Set = dependent-universal-property-trunc

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
equiv-dependent-universal-property-trunc-Set =
  equiv-dependent-universal-property-trunc

module _
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2)
  (f : (x : A) → type-Set (B (unit-trunc-Set x)))
  where

  Π-trunc-Set : UU (l1 ⊔ l2)
  Π-trunc-Set =
    Σ ( (x : type-trunc-Set A) → type-Set (B x))
      ( λ g → g ∘ unit-trunc-Set ~ f)

  function-dependent-universal-property-trunc-Set :
    (x : type-trunc-Set A) → type-Set (B x)
  function-dependent-universal-property-trunc-Set =
    function-dependent-universal-property-trunc B f

  compute-dependent-universal-property-trunc-Set :
    function-dependent-universal-property-trunc-Set ∘ unit-trunc-Set ~ f
  compute-dependent-universal-property-trunc-Set =
    htpy-dependent-universal-property-trunc B f

  apply-dependent-universal-property-trunc-Set' :
    (x : type-trunc-Set A) → type-Set (B x)
  apply-dependent-universal-property-trunc-Set' =
    map-inv-equiv (equiv-dependent-universal-property-trunc-Set B) f
```

### The universal property of set truncations

```agda
universal-property-trunc-Set :
  {l1 : Level} (A : UU l1) →
  universal-property-set-truncation (trunc-Set A) (unit-trunc-Set)
universal-property-trunc-Set A = universal-property-trunc zero-𝕋 A

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2)
  where

  equiv-universal-property-trunc-Set :
    (type-trunc-Set A → type-Set B) ≃ (A → type-Set B)
  equiv-universal-property-trunc-Set = equiv-universal-property-trunc A B

  apply-universal-property-trunc-Set :
    (t : type-trunc-Set A) → (A → type-Set B) → type-Set B
  apply-universal-property-trunc-Set t f = map-universal-property-trunc B f t

  map-universal-property-trunc-Set :
    (A → type-Set B) → hom-Set (trunc-Set A) B
  map-universal-property-trunc-Set = map-universal-property-trunc B

  triangle-universal-property-trunc-Set :
    (f : A → type-Set B) →
    map-universal-property-trunc-Set f ∘ unit-trunc-Set ~ f
  triangle-universal-property-trunc-Set = triangle-universal-property-trunc B
  Map-trunc-Set : (f : A → type-Set B) → UU (l1 ⊔ l2)
  Map-trunc-Set f =
    Σ (type-trunc-Set A → type-Set B) (λ g → g ∘ unit-trunc-Set ~ f)

apply-universal-property-trunc-Set' :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Set A) (B : Set l2) →
  (A → type-Set B) → type-Set B
apply-universal-property-trunc-Set' t B f =
  map-universal-property-trunc-Set B f t
```

### The set truncation of `X` is the set quotient by the mere equality relation

```agda
reflecting-map-mere-eq-unit-trunc-Set :
  {l : Level} (A : UU l) →
  reflecting-map-equivalence-relation
    ( mere-eq-equivalence-relation A)
    ( type-trunc-Set A)
reflecting-map-mere-eq-unit-trunc-Set A =
  pair unit-trunc-Set (reflects-mere-eq (trunc-Set A) unit-trunc-Set)

abstract
  is-set-quotient-trunc-Set :
    {l1 : Level} (A : UU l1) →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( trunc-Set A)
      ( reflecting-map-mere-eq-unit-trunc-Set A)
  is-set-quotient-trunc-Set A =
    is-set-quotient-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( λ {l} → is-set-truncation-trunc-Set A)

module _
  {l : Level}
  where

  abstract
    is-surjective-and-effective-unit-trunc-Set :
      (A : UU l) →
      is-surjective-and-effective
        ( mere-eq-equivalence-relation A)
        ( unit-trunc-Set)
    is-surjective-and-effective-unit-trunc-Set A =
      is-surjective-and-effective-is-set-quotient
        ( mere-eq-equivalence-relation A)
        ( trunc-Set A)
        ( unit-trunc-Set ,
          reflects-mere-eq (trunc-Set A) unit-trunc-Set)
        ( λ {l} → is-set-quotient-trunc-Set A)

  abstract
    is-surjective-unit-trunc-Set :
      (A : UU l) → is-surjective (unit-trunc-Set {A = A})
    is-surjective-unit-trunc-Set A =
      pr1 (is-surjective-and-effective-unit-trunc-Set A)

  abstract
    is-effective-unit-trunc-Set :
      (A : UU l) →
      is-effective (mere-eq-equivalence-relation A) (unit-trunc-Set {A = A})
    is-effective-unit-trunc-Set A =
      pr2 (is-surjective-and-effective-unit-trunc-Set A)

  abstract
    apply-effectiveness-unit-trunc-Set :
      {A : UU l} {x y : A} → unit-trunc-Set x ＝ unit-trunc-Set y → mere-eq x y
    apply-effectiveness-unit-trunc-Set {A = A} {x} {y} =
      map-equiv (is-effective-unit-trunc-Set A x y)

  abstract
    apply-effectiveness-unit-trunc-Set' :
      {A : UU l} {x y : A} → mere-eq x y → unit-trunc-Set x ＝ unit-trunc-Set y
    apply-effectiveness-unit-trunc-Set' {A = A} {x} {y} =
      map-inv-equiv (is-effective-unit-trunc-Set A x y)

  emb-trunc-Set : (A : UU l) → type-trunc-Set A ↪ (A → Prop l)
  emb-trunc-Set A =
    emb-is-surjective-and-effective
      ( mere-eq-equivalence-relation A)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( is-surjective-and-effective-unit-trunc-Set A)

  hom-slice-trunc-Set :
    (A : UU l) → hom-slice (mere-eq-Prop {A = A}) (map-emb (emb-trunc-Set A))
  pr1 (hom-slice-trunc-Set A) = unit-trunc-Set
  pr2 (hom-slice-trunc-Set A) =
    triangle-emb-is-surjective-and-effective
      ( mere-eq-equivalence-relation A)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( is-surjective-and-effective-unit-trunc-Set A)

  abstract
    is-image-trunc-Set :
      (A : UU l) →
      is-image
        ( mere-eq-Prop {A = A})
        ( emb-trunc-Set A)
        ( hom-slice-trunc-Set A)
    is-image-trunc-Set A =
      is-image-is-surjective-and-effective
        ( mere-eq-equivalence-relation A)
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( is-surjective-and-effective-unit-trunc-Set A)
```

### Uniqueness of `trunc-Set`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  {h : hom-Set B (trunc-Set A)} (H : h ∘ f ~ unit-trunc-Set)
  where

  abstract
    is-equiv-is-set-truncation' : is-set-truncation B f → is-equiv h
    is-equiv-is-set-truncation' Sf =
      is-equiv-is-set-truncation-is-set-truncation
        ( B)
        ( f)
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( H)
        ( Sf)
        ( λ {h} → is-set-truncation-trunc-Set A)

  abstract
    is-set-truncation-is-equiv' :
      is-equiv h → is-set-truncation B f
    is-set-truncation-is-equiv' Eh =
      is-set-truncation-is-equiv-is-set-truncation
        ( B)
        ( f)
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( H)
        ( λ {l} → is-set-truncation-trunc-Set A)
        ( Eh)

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  {h : hom-Set (trunc-Set A) B} (H : h ∘ unit-trunc-Set ~ f)
  where

  abstract
    is-equiv-is-set-truncation : is-set-truncation B f → is-equiv h
    is-equiv-is-set-truncation Sf =
      is-equiv-is-set-truncation-is-set-truncation
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( B)
        ( f)
        ( H)
        ( λ {l} → is-set-truncation-trunc-Set A)
        ( Sf)

  abstract
    is-set-truncation-is-equiv :
      is-equiv h → is-set-truncation B f
    is-set-truncation-is-equiv Eh =
      is-set-truncation-is-set-truncation-is-equiv
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( B)
        ( f)
        ( H)
        ( Eh)
        ( λ {l} → is-set-truncation-trunc-Set A)

is-equiv-unit-trunc-Set :
  {l : Level} (A : Set l) → is-equiv (unit-trunc-Set {A = type-Set A})
is-equiv-unit-trunc-Set = is-equiv-unit-trunc

equiv-unit-trunc-Set :
  {l : Level} (A : Set l) → type-Set A ≃ type-trunc-Set (type-Set A)
equiv-unit-trunc-Set = equiv-unit-trunc

equiv-unit-trunc-empty-Set : empty ≃ type-trunc-Set empty
equiv-unit-trunc-empty-Set = equiv-unit-trunc-Set empty-Set

abstract
  is-empty-trunc-Set :
    {l : Level} {A : UU l} → is-empty A → is-empty (type-trunc-Set A)
  is-empty-trunc-Set f x = apply-universal-property-trunc-Set' x empty-Set f

abstract
  is-empty-is-empty-trunc-Set :
    {l : Level} {A : UU l} → is-empty (type-trunc-Set A) → is-empty A
  is-empty-is-empty-trunc-Set f = f ∘ unit-trunc-Set

equiv-unit-trunc-unit-Set : unit ≃ type-trunc-Set unit
equiv-unit-trunc-unit-Set = equiv-unit-trunc-Set unit-Set

abstract
  is-contr-trunc-Set :
    {l : Level} {A : UU l} → is-contr A → is-contr (type-trunc-Set A)
  is-contr-trunc-Set {l} {A} H =
    is-contr-equiv'
      ( A)
      ( equiv-unit-trunc-Set (pair A (is-set-is-contr H)))
      ( H)

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (Sf : is-set-truncation B f)
  where

  abstract
    uniqueness-trunc-Set :
      is-contr
        ( Σ (type-trunc-Set A ≃ type-Set B)
        ( λ e → map-equiv e ∘ unit-trunc-Set ~ f))
    uniqueness-trunc-Set =
      uniqueness-set-truncation (trunc-Set A) unit-trunc-Set B f
        ( λ {l} → is-set-truncation-trunc-Set A)
        ( Sf)

  equiv-uniqueness-trunc-Set : type-trunc-Set A ≃ type-Set B
  equiv-uniqueness-trunc-Set = pr1 (center uniqueness-trunc-Set)

  map-equiv-uniqueness-trunc-Set : type-trunc-Set A → type-Set B
  map-equiv-uniqueness-trunc-Set = map-equiv equiv-uniqueness-trunc-Set

  triangle-uniqueness-trunc-Set :
    map-equiv-uniqueness-trunc-Set ∘ unit-trunc-Set ~ f
  triangle-uniqueness-trunc-Set = pr2 (center uniqueness-trunc-Set)

module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (Sf : is-set-truncation B f)
  where

  abstract
    uniqueness-trunc-Set' :
      is-contr
        ( Σ ( type-Set B ≃ type-trunc-Set A)
            ( λ e → map-equiv e ∘ f ~ unit-trunc-Set))
    uniqueness-trunc-Set' =
      uniqueness-set-truncation B f (trunc-Set A) unit-trunc-Set Sf
        ( λ {l} → is-set-truncation-trunc-Set A)

  equiv-uniqueness-trunc-Set' : type-Set B ≃ type-trunc-Set A
  equiv-uniqueness-trunc-Set' = pr1 (center uniqueness-trunc-Set')

  map-equiv-uniqueness-trunc-Set' : type-Set B → type-trunc-Set A
  map-equiv-uniqueness-trunc-Set' =
    map-equiv equiv-uniqueness-trunc-Set'

  triangle-uniqueness-trunc-Set' :
    map-equiv-uniqueness-trunc-Set' ∘ f ~ unit-trunc-Set
  triangle-uniqueness-trunc-Set' = pr2 (center uniqueness-trunc-Set')
```

### The set truncation of a set is equivalent to the set

```agda
module _
  {l : Level} (A : Set l)
  where

  equiv-unit-trunc-set : type-Set A ≃ type-trunc-Set (type-Set A)
  equiv-unit-trunc-set = equiv-unit-trunc A
```

### Distributive of set truncation over coproduct

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-coproduct-Set :
      is-contr
        ( Σ ( equiv-Set
              ( trunc-Set (A + B))
              ( coproduct-Set (trunc-Set A) (trunc-Set B)))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-coproduct unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-coproduct-Set =
      uniqueness-trunc-Set
        ( coproduct-Set (trunc-Set A) (trunc-Set B))
        ( map-coproduct unit-trunc-Set unit-trunc-Set)
        ( λ {l} C →
          is-equiv-right-factor
            ( ev-inl-inr (λ x → type-Set C))
            ( precomp-Set (map-coproduct unit-trunc-Set unit-trunc-Set) C)
            ( universal-property-coproduct (type-Set C))
            ( is-equiv-comp
              ( map-product
                ( precomp-Set unit-trunc-Set C)
                ( precomp-Set unit-trunc-Set C))
              ( ev-inl-inr (λ x → type-Set C))
              ( universal-property-coproduct (type-Set C))
              ( is-equiv-map-product
                ( precomp-Set unit-trunc-Set C)
                ( precomp-Set unit-trunc-Set C)
                ( is-set-truncation-trunc-Set A C)
                ( is-set-truncation-trunc-Set B C))))

  equiv-distributive-trunc-coproduct-Set :
    equiv-Set (trunc-Set (A + B)) (coproduct-Set (trunc-Set A) (trunc-Set B))
  equiv-distributive-trunc-coproduct-Set =
    pr1 (center distributive-trunc-coproduct-Set)

  map-equiv-distributive-trunc-coproduct-Set :
    hom-Set (trunc-Set (A + B)) (coproduct-Set (trunc-Set A) (trunc-Set B))
  map-equiv-distributive-trunc-coproduct-Set =
    map-equiv equiv-distributive-trunc-coproduct-Set

  triangle-distributive-trunc-coproduct-Set :
    ( map-equiv-distributive-trunc-coproduct-Set ∘ unit-trunc-Set) ~
    ( map-coproduct unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-coproduct-Set =
    pr2 (center distributive-trunc-coproduct-Set)
```

### Set truncations of Σ-types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  abstract
    trunc-Σ-Set :
      is-contr
        ( Σ ( type-trunc-Set (Σ A B) ≃
              type-trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))))
    trunc-Σ-Set =
      uniqueness-trunc-Set
        ( trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
        ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
        ( λ {l} C →
          is-equiv-right-factor
            ( ev-pair)
            ( precomp-Set (unit-trunc-Set ∘ tot (λ x → unit-trunc-Set)) C)
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( equiv-Π-equiv-family
                  ( λ x → equiv-universal-property-trunc-Set C)) ∘e
                ( equiv-ev-pair) ∘e
                ( equiv-universal-property-trunc-Set C))
              ( refl-htpy)))

  equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) ≃ type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  equiv-trunc-Σ-Set = pr1 (center trunc-Σ-Set)

  map-equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) → type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  map-equiv-trunc-Σ-Set = map-equiv equiv-trunc-Σ-Set
```

### `trunc-Set` distributes over products

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-product-Set :
      is-contr
        ( Σ ( type-trunc-Set (A × B) ≃ (type-trunc-Set A × type-trunc-Set B))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-product unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-product-Set =
      uniqueness-trunc-Set
        ( product-Set (trunc-Set A) (trunc-Set B))
        ( map-product unit-trunc-Set unit-trunc-Set)
        ( λ {l} C →
          is-equiv-right-factor
            ( ev-pair)
            ( precomp-Set (map-product unit-trunc-Set unit-trunc-Set) C)
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( equiv-universal-property-trunc-Set (Π-Set' B (λ y → C))) ∘e
                ( equiv-postcomp
                  ( type-trunc-Set A)
                  ( equiv-universal-property-trunc-Set C)) ∘e
                ( equiv-ev-pair))
              ( refl-htpy)))

  equiv-distributive-trunc-product-Set :
    type-trunc-Set (A × B) ≃ (type-trunc-Set A × type-trunc-Set B)
  equiv-distributive-trunc-product-Set =
    pr1 (center distributive-trunc-product-Set)

  map-equiv-distributive-trunc-product-Set :
    type-trunc-Set (A × B) → type-trunc-Set A × type-trunc-Set B
  map-equiv-distributive-trunc-product-Set =
    map-equiv equiv-distributive-trunc-product-Set

  map-inv-equiv-distributive-trunc-product-Set :
    type-trunc-Set A × type-trunc-Set B → type-trunc-Set (A × B)
  map-inv-equiv-distributive-trunc-product-Set =
    map-inv-equiv equiv-distributive-trunc-product-Set

  triangle-distributive-trunc-product-Set :
    ( map-equiv-distributive-trunc-product-Set ∘ unit-trunc-Set) ~
    ( map-product unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-product-Set =
    pr2 (center distributive-trunc-product-Set)
```
