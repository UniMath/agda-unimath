# Decidable retracts of types

```agda
module foundation-core.decidable-retracts-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.complements-images
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.retracts-of-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.postcomposition-functions
open import foundation-core.precomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A {{#concept "decidable retract" Disambiguation="of types"}} `A` of a type `B`
is the data of pair of maps

```text
      i       r
  A ----> B ----> A
```

such that `r ∘ i ~ id`, where `i` is a
[decidable embedding](foundation.decidable-embeddings.md). Equivalently, it is a
display of `B` as a [coproduct](foundation.coproduct-types.md) `A + C` together
with a map `C → A`.

## Definitions

### The type of witnesses that `A` is a retract of `B`

```agda
decidable-retract : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
decidable-retract B A =
  Σ (retract B A) (λ R → is-decidable-emb (inclusion-retract R))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : decidable-retract B A)
  where

  retract-decidable-retract : retract B A
  retract-decidable-retract = pr1 R

  inclusion-decidable-retract : A → B
  inclusion-decidable-retract = inclusion-retract retract-decidable-retract

  retraction-decidable-retract : retraction inclusion-decidable-retract
  retraction-decidable-retract = retraction-retract retract-decidable-retract

  map-retraction-decidable-retract : B → A
  map-retraction-decidable-retract =
    map-retraction-retract retract-decidable-retract

  is-retraction-map-retraction-decidable-retract :
    is-section map-retraction-decidable-retract inclusion-decidable-retract
  is-retraction-map-retraction-decidable-retract =
    is-retraction-map-retraction-retract retract-decidable-retract

  section-decidable-retract : section map-retraction-decidable-retract
  section-decidable-retract = section-retract retract-decidable-retract

  is-decidable-emb-inclusion-decidable-retract :
    is-decidable-emb inclusion-decidable-retract
  is-decidable-emb-inclusion-decidable-retract = pr2 R

  decidable-emb-inclusion-decidable-retract : A ↪ᵈ B
  decidable-emb-inclusion-decidable-retract =
    ( inclusion-decidable-retract ,
      is-decidable-emb-inclusion-decidable-retract)
```

### The type of decidable retracts of a type

```agda
decidable-retracts : {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
decidable-retracts l2 A = Σ (UU l2) (decidable-retract A)

module _
  {l1 l2 : Level} {A : UU l1} (R : decidable-retracts l2 A)
  where

  type-decidable-retracts : UU l2
  type-decidable-retracts = pr1 R

  decidable-retract-decidable-retracts :
    decidable-retract A type-decidable-retracts
  decidable-retract-decidable-retracts = pr2 R

  retract-decidable-retracts : type-decidable-retracts retract-of A
  retract-decidable-retracts =
    retract-decidable-retract decidable-retract-decidable-retracts

  inclusion-decidable-retracts : type-decidable-retracts → A
  inclusion-decidable-retracts =
    inclusion-retract retract-decidable-retracts

  retraction-decidable-retracts : retraction inclusion-decidable-retracts
  retraction-decidable-retracts =
    retraction-retract retract-decidable-retracts

  map-retraction-decidable-retracts : A → type-decidable-retracts
  map-retraction-decidable-retracts =
    map-retraction-retract retract-decidable-retracts

  is-retraction-map-retraction-decidable-retracts :
    is-section map-retraction-decidable-retracts inclusion-decidable-retracts
  is-retraction-map-retraction-decidable-retracts =
    is-retraction-map-retraction-retract retract-decidable-retracts

  section-decidable-retracts : section map-retraction-decidable-retracts
  section-decidable-retracts =
    section-retract retract-decidable-retracts
```

### The identity decidable retract

```agda
module _
  {l : Level} {A : UU l}
  where

  id-decidable-retract : decidable-retract A A
  id-decidable-retract = (id-retract , is-decidable-emb-id)
```

### Composition of decidable retracts

```agda
comp-decidable-retract :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  decidable-retract C B → decidable-retract B A → decidable-retract C A
comp-decidable-retract (r , H) (r' , H') =
  ( comp-retract r r' , is-decidable-emb-comp H H')
```

## Properties

### The associated coproduct decomposition of a decidable retract

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coproduct-decomposition-nonim-decidable-retract :
    (R : decidable-retract A B) → A ≃ B + nonim (inclusion-decidable-retract R)
  coproduct-decomposition-nonim-decidable-retract R =
    coproduct-decomposition-codomain-decidable-emb
      ( decidable-emb-inclusion-decidable-retract R)
```

### The coproduct decomposition characterization of decidable retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-coproduct-decomposition-decidable-retract :
    decidable-retract A B →
    Σ (UU (l1 ⊔ l2)) (λ C → (A ≃ B + C) × (C → B))
  map-coproduct-decomposition-decidable-retract R =
    ( nonim (inclusion-decidable-retract R) ,
      coproduct-decomposition-nonim-decidable-retract R ,
      ( map-retraction-decidable-retract R ∘
        inclusion-nonim (inclusion-decidable-retract R)))

  map-inv-coproduct-decomposition-decidable-retract :
    Σ (UU (l1 ⊔ l2)) (λ C → (A ≃ B + C) × (C → B)) →
    decidable-retract A B
  map-inv-coproduct-decomposition-decidable-retract (C , e , f) =
    ( map-inv-equiv e ∘ inl ,
      rec-coproduct id f ∘ map-equiv e ,
      is-retraction-map-retraction-comp
        ( map-inv-equiv e)
        ( inl)
        ( map-equiv e , is-section-map-inv-equiv e)
        ( rec-coproduct id f , refl-htpy)) ,
      is-decidable-emb-comp
        ( is-decidable-emb-is-equiv (is-equiv-map-inv-equiv e))
        ( is-decidable-emb-inl)
```

> It remains to show that these two constructions form mutual inverses.
