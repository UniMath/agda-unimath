# Equivalences of polynomial endofunctors

```agda
module trees.equivalences-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.torsorial-type-families

open import trees.cartesian-morphisms-polynomial-endofunctors
open import trees.morphisms-polynomial-endofunctors
open import trees.natural-transformations-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

Given two [polynomial endofunctors](trees.polynomial-endofunctors.md)
$P ≐ (A \mathbin{◃} B)$ and $Q ≐ (C \mathbin{◃} D)$, a
[morphism](trees.morphisms-polynomial-endofunctors.md) $α : P → Q$ is an
{{#concept "equivalence" Disambiguation="of polynomial endofunctors of types" Agda=is-equiv-hom-polynomial-endofunctor Agda=equiv-polynomial-endofunctor}}
if the map on shapes $α₀ : A → B$ is an equivalence and the family of maps on
positions

$$α₁ : (a : A) → D (α₀ a) → B a$$

is a family of [equivalences](foundation-core.equivalences.md).

## Definitions

### The predicate of being an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : hom-polynomial-endofunctor P Q)
  where

  is-equiv-hom-polynomial-endofunctor :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-polynomial-endofunctor =
    ( is-equiv (shape-hom-polynomial-endofunctor P Q α)) ×
    ( (a : shape-polynomial-endofunctor P) →
      is-equiv (position-hom-polynomial-endofunctor P Q α a))

  abstract
    is-prop-is-equiv-hom-polynomial-endofunctor :
      is-prop is-equiv-hom-polynomial-endofunctor
    is-prop-is-equiv-hom-polynomial-endofunctor =
      is-prop-product
        ( is-property-is-equiv (shape-hom-polynomial-endofunctor P Q α))
        ( is-prop-is-cartesian-hom-polynomial-endofunctor P Q α)

  is-equiv-hom-polynomial-endofunctor-Prop :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-polynomial-endofunctor-Prop =
    ( is-equiv-hom-polynomial-endofunctor ,
      is-prop-is-equiv-hom-polynomial-endofunctor)
```

### The type of equivalences

```agda
equiv-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-polynomial-endofunctor P Q =
  Σ ( hom-polynomial-endofunctor P Q)
    ( is-equiv-hom-polynomial-endofunctor P Q)
```

The underlying morphism.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : equiv-polynomial-endofunctor P Q)
  where

  hom-equiv-polynomial-endofunctor : hom-polynomial-endofunctor P Q
  hom-equiv-polynomial-endofunctor = pr1 α

  shape-equiv-polynomial-endofunctor :
    shape-polynomial-endofunctor P → shape-polynomial-endofunctor Q
  shape-equiv-polynomial-endofunctor =
    shape-hom-polynomial-endofunctor P Q
      ( hom-equiv-polynomial-endofunctor)

  position-equiv-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor P) →
    position-polynomial-endofunctor Q
      ( shape-hom-polynomial-endofunctor P Q
        ( hom-equiv-polynomial-endofunctor)
        ( a)) →
    position-polynomial-endofunctor P a
  position-equiv-polynomial-endofunctor =
    position-hom-polynomial-endofunctor P Q
      hom-equiv-polynomial-endofunctor

  is-equiv-hom-equiv-polynomial-endofunctor :
    is-equiv-hom-polynomial-endofunctor P Q
      hom-equiv-polynomial-endofunctor
  is-equiv-hom-equiv-polynomial-endofunctor = pr2 α

  is-cartesian-hom-equiv-polynomial-endofunctor :
    is-cartesian-hom-polynomial-endofunctor P Q hom-equiv-polynomial-endofunctor
  is-cartesian-hom-equiv-polynomial-endofunctor =
    pr2 is-equiv-hom-equiv-polynomial-endofunctor

  is-equiv-shape-equiv-polynomial-endofunctor :
    is-equiv shape-equiv-polynomial-endofunctor
  is-equiv-shape-equiv-polynomial-endofunctor =
    pr1 is-equiv-hom-equiv-polynomial-endofunctor

  equiv-shape-equiv-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor P) →
    position-polynomial-endofunctor Q
      ( shape-hom-polynomial-endofunctor P Q
        ( hom-equiv-polynomial-endofunctor)
        ( a)) ≃
    position-polynomial-endofunctor P a
  equiv-shape-equiv-polynomial-endofunctor a =
    ( position-equiv-polynomial-endofunctor a ,
      is-cartesian-hom-equiv-polynomial-endofunctor a)

  equiv-position-equiv-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor P) →
    position-polynomial-endofunctor Q
      ( shape-hom-polynomial-endofunctor P Q
        ( hom-equiv-polynomial-endofunctor)
        ( a)) ≃
    position-polynomial-endofunctor P a
  equiv-position-equiv-polynomial-endofunctor a =
    ( position-equiv-polynomial-endofunctor a ,
      is-cartesian-hom-equiv-polynomial-endofunctor a)
```

The underlying natural transformation.

```agda
  type-equiv-polynomial-endofunctor :
    {l5 : Level} {X : UU l5} →
    type-polynomial-endofunctor P X → type-polynomial-endofunctor Q X
  type-equiv-polynomial-endofunctor =
    type-hom-polynomial-endofunctor P Q
      hom-equiv-polynomial-endofunctor

  naturality-equiv-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    coherence-square-maps
      ( map-polynomial-endofunctor P f)
      ( type-equiv-polynomial-endofunctor)
      ( type-equiv-polynomial-endofunctor)
      ( map-polynomial-endofunctor Q f)
  naturality-equiv-polynomial-endofunctor =
    naturality-hom-polynomial-endofunctor P Q
      hom-equiv-polynomial-endofunctor

  natural-transformation-equiv-polynomial-endofunctor :
    {l : Level} → natural-transformation-polynomial-endofunctor l P Q
  natural-transformation-equiv-polynomial-endofunctor =
    natural-transformation-hom-polynomial-endofunctor P Q
      hom-equiv-polynomial-endofunctor

  hom-arrow-equiv-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    hom-arrow (map-polynomial-endofunctor P f) (map-polynomial-endofunctor Q f)
  hom-arrow-equiv-polynomial-endofunctor =
    hom-arrow-hom-polynomial-endofunctor P Q
      hom-equiv-polynomial-endofunctor

  is-equiv-type-equiv-polynomial-endofunctor :
    {l5 : Level} {X : UU l5} →
    is-equiv (type-equiv-polynomial-endofunctor {X = X})
  is-equiv-type-equiv-polynomial-endofunctor {X = X} =
    is-equiv-map-Σ
      (λ c → position-polynomial-endofunctor Q c → X)
      ( is-equiv-shape-equiv-polynomial-endofunctor)
      ( λ a →
        is-equiv-precomp-is-equiv
          ( position-equiv-polynomial-endofunctor a)
          ( is-cartesian-hom-equiv-polynomial-endofunctor a)
          ( X))

  equiv-type-equiv-polynomial-endofunctor :
    {l5 : Level} (X : UU l5) →
    type-polynomial-endofunctor P X ≃ type-polynomial-endofunctor Q X
  equiv-type-equiv-polynomial-endofunctor X =
    ( type-equiv-polynomial-endofunctor ,
      is-equiv-type-equiv-polynomial-endofunctor)

  equiv-arrow-equiv-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    equiv-arrow
      ( map-polynomial-endofunctor P f)
      ( map-polynomial-endofunctor Q f)
  equiv-arrow-equiv-polynomial-endofunctor {X = X} {Y} f =
    ( equiv-type-equiv-polynomial-endofunctor X ,
      equiv-type-equiv-polynomial-endofunctor Y ,
      naturality-equiv-polynomial-endofunctor f)

  cone-equiv-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    cone
      ( type-equiv-polynomial-endofunctor)
      ( map-polynomial-endofunctor Q f)
      ( type-polynomial-endofunctor P X)
  cone-equiv-polynomial-endofunctor =
    cone-hom-polynomial-endofunctor P Q hom-equiv-polynomial-endofunctor
```

### The identity equivalence

```agda
id-equiv-polynomial-endofunctor :
  {l1 l2 : Level}
  (P : polynomial-endofunctor l1 l2) →
  equiv-polynomial-endofunctor P P
id-equiv-polynomial-endofunctor P =
  ( id-hom-polynomial-endofunctor P , is-equiv-id , (λ a → is-equiv-id))
```

### Composition of equivalences

```agda
comp-equiv-polynomial-endofunctor :
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (R : polynomial-endofunctor l5 l6) →
  equiv-polynomial-endofunctor Q R →
  equiv-polynomial-endofunctor P Q →
  equiv-polynomial-endofunctor P R
comp-equiv-polynomial-endofunctor
  P Q R ((β₀ , β₁) , (H₀ , H₁)) ((α₀ , α₁) , (K₀ , K₁)) =
  ( ( comp-hom-polynomial-endofunctor P Q R (β₀ , β₁) (α₀ , α₁)) ,
    ( is-equiv-comp β₀ α₀ K₀ H₀) ,
    ( λ a → is-equiv-comp (α₁ a) (β₁ (α₀ a)) (H₁ (α₀ a)) (K₁ a)))
```

## Properties

### A computation of the type of equivalences

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  where

  equiv-polynomial-endofunctor' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-polynomial-endofunctor' =
    Σ ( shape-polynomial-endofunctor P ≃ shape-polynomial-endofunctor Q)
      ( λ α₀ →
        ((a : shape-polynomial-endofunctor P) →
          position-polynomial-endofunctor Q (map-equiv α₀ a) ≃
          position-polynomial-endofunctor P a))

  compute-equiv-polynomial-endofunctor :
    equiv-polynomial-endofunctor P Q ≃
    equiv-polynomial-endofunctor'
  pr1 compute-equiv-polynomial-endofunctor ((α₀ , α₁) , (H₀ , H₁)) =
    ((α₀ , H₀) , (λ a → (α₁ a , H₁ a)))
  pr2 compute-equiv-polynomial-endofunctor =
    is-equiv-is-invertible
      ( λ ((α₀ , H₀) , αH₁) → (α₀ , pr1 ∘ αH₁) , (H₀ , pr2 ∘ αH₁))
      ( refl-htpy)
      ( refl-htpy)

id-equiv-polynomial-endofunctor' :
  {l1 l2 : Level}
  (P : polynomial-endofunctor l1 l2) → equiv-polynomial-endofunctor' P P
id-equiv-polynomial-endofunctor' P = (id-equiv , λ a → id-equiv)
```

### Equivalences characterize equality of polynomial endofunctors

```agda
module _
  {l1 l2 : Level}
  where

  abstract
    is-torsorial-equiv-polynomial-endofunctor' :
      (P : polynomial-endofunctor l1 l2) →
      is-torsorial (equiv-polynomial-endofunctor' {l1} {l2} {l1} {l2} P)
    is-torsorial-equiv-polynomial-endofunctor' P =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (shape-polynomial-endofunctor P))
        ( shape-polynomial-endofunctor P , id-equiv)
        ( is-torsorial-Eq-Π
          ( λ a → is-torsorial-equiv' (position-polynomial-endofunctor P a)))

  abstract
    is-torsorial-equiv-polynomial-endofunctor :
      (P : polynomial-endofunctor l1 l2) →
      is-torsorial (equiv-polynomial-endofunctor {l1} {l2} {l1} {l2} P)
    is-torsorial-equiv-polynomial-endofunctor P =
      is-contr-equiv
        ( Σ (polynomial-endofunctor l1 l2) (equiv-polynomial-endofunctor' P))
        ( equiv-tot (compute-equiv-polynomial-endofunctor P))
        ( is-torsorial-equiv-polynomial-endofunctor' P)

  equiv-eq-polynomial-endofunctor' :
    (P Q : polynomial-endofunctor l1 l2) →
    P ＝ Q → equiv-polynomial-endofunctor' P Q
  equiv-eq-polynomial-endofunctor' P .P refl =
    id-equiv-polynomial-endofunctor' P

  equiv-eq-polynomial-endofunctor :
    (P Q : polynomial-endofunctor l1 l2) →
    P ＝ Q → equiv-polynomial-endofunctor P Q
  equiv-eq-polynomial-endofunctor P .P refl =
    id-equiv-polynomial-endofunctor P

  abstract
    is-equiv-equiv-eq-polynomial-endofunctor' :
      (P Q : polynomial-endofunctor l1 l2) →
      is-equiv (equiv-eq-polynomial-endofunctor' P Q)
    is-equiv-equiv-eq-polynomial-endofunctor' P =
      fundamental-theorem-id
        ( is-torsorial-equiv-polynomial-endofunctor' P)
        ( equiv-eq-polynomial-endofunctor' P)

  abstract
    is-equiv-equiv-eq-polynomial-endofunctor :
      (P Q : polynomial-endofunctor l1 l2) →
      is-equiv (equiv-eq-polynomial-endofunctor P Q)
    is-equiv-equiv-eq-polynomial-endofunctor P =
      fundamental-theorem-id
        ( is-torsorial-equiv-polynomial-endofunctor P)
        ( equiv-eq-polynomial-endofunctor P)

  extensionality-polynomial-endofunctor' :
    (P Q : polynomial-endofunctor l1 l2) →
    (P ＝ Q) ≃ (equiv-polynomial-endofunctor' P Q)
  extensionality-polynomial-endofunctor' P Q =
    ( equiv-eq-polynomial-endofunctor' P Q ,
      is-equiv-equiv-eq-polynomial-endofunctor' P Q)

  extensionality-polynomial-endofunctor :
    (P Q : polynomial-endofunctor l1 l2) →
    (P ＝ Q) ≃ (equiv-polynomial-endofunctor P Q)
  extensionality-polynomial-endofunctor P Q =
    ( equiv-eq-polynomial-endofunctor P Q ,
      is-equiv-equiv-eq-polynomial-endofunctor P Q)

  eq-equiv-polynomial-endofunctor' :
    (P Q : polynomial-endofunctor l1 l2) →
    equiv-polynomial-endofunctor' P Q → P ＝ Q
  eq-equiv-polynomial-endofunctor' P Q =
    map-inv-equiv (extensionality-polynomial-endofunctor' P Q)

  eq-equiv-polynomial-endofunctor :
    (P Q : polynomial-endofunctor l1 l2) →
    equiv-polynomial-endofunctor P Q → P ＝ Q
  eq-equiv-polynomial-endofunctor P Q =
    map-inv-equiv (extensionality-polynomial-endofunctor P Q)
```
