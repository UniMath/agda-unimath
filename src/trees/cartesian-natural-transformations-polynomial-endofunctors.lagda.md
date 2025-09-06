# Cartesian natural transformations between polynomial endofunctors

```agda
module trees.cartesian-natural-transformations-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.cartesian-morphisms-arrows
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.morphisms-arrows
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equality-dependent-pair-types
open import foundation-core.retractions
open import foundation-core.torsorial-type-families

open import trees.natural-transformations-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

Given two [polynomial endofunctors](trees.polynomial-endofunctors.md)
$𝑃 ≐ (A ◃ B)$ and $𝑄 ≐ (C ◃ D)$, then a
[natural transformation](trees.natural-transformations-polynomial-endofunctors.md)
$α$ between them is
{{#concept "cartesian" Disambiguation="natural transformations of polynomial endofunctors of types" Agda=is-cartesian-natural-transformation-polynomial-endofunctor}}

if every naturality square

```text
              α(X)
     𝑃(X) -----------> 𝑄(X)
       |                |
       |                |
  𝑃(f) |                | 𝑄(f)
       |                |
       ∨                ∨
     𝑃(Y) -----------> 𝑄(Y)
              α(Y)
```

is a [pullback](foundation-core.pullbacks.md).

## Definitions

### The cartesianness predicate on natural transformations between polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 l : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l 𝑃 𝑄)
  where

  is-cartesian-natural-transformation-polynomial-endofunctor :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  is-cartesian-natural-transformation-polynomial-endofunctor =
    {X Y : UU l} (f : X → Y) →
    is-cartesian-hom-arrow
      ( map-polynomial-endofunctor 𝑃 f)
      ( map-polynomial-endofunctor 𝑄 f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α f)

  is-prop-is-cartesian-natural-transformation-polynomial-endofunctor :
    is-prop is-cartesian-natural-transformation-polynomial-endofunctor
  is-prop-is-cartesian-natural-transformation-polynomial-endofunctor =
    is-prop-implicit-Π
      ( λ X →
        is-prop-implicit-Π
          ( λ Y →
            is-prop-Π
              ( λ f →
                is-prop-is-cartesian-hom-arrow
                  ( map-polynomial-endofunctor 𝑃 f)
                  ( map-polynomial-endofunctor 𝑄 f)
                  ( hom-arrow-natural-transformation-polynomial-endofunctor 𝑃 𝑄
                    ( α)
                    ( f)))))

  is-cartesian-natural-transformation-polynomial-endofunctor-Prop :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  is-cartesian-natural-transformation-polynomial-endofunctor-Prop =
    ( is-cartesian-natural-transformation-polynomial-endofunctor ,
      is-prop-is-cartesian-natural-transformation-polynomial-endofunctor)
```

### Cartesian natural transformations between polynomial endofunctors

```agda
cartesian-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (l : Level) →
  polynomial-endofunctor l1 l2 →
  polynomial-endofunctor l3 l4 →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
cartesian-natural-transformation-polynomial-endofunctor l 𝑃 𝑄 =
  Σ ( natural-transformation-polynomial-endofunctor l 𝑃 𝑄)
    ( is-cartesian-natural-transformation-polynomial-endofunctor 𝑃 𝑄)

module _
  {l1 l2 l3 l4 l : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : cartesian-natural-transformation-polynomial-endofunctor l 𝑃 𝑄)
  where

  natural-transformation-cartesian-natural-transformation-polynomial-endofunctor :
    natural-transformation-polynomial-endofunctor l 𝑃 𝑄
  natural-transformation-cartesian-natural-transformation-polynomial-endofunctor =
    pr1 α

  type-cartesian-natural-transformation-polynomial-endofunctor :
    {X : UU l} →
    type-polynomial-endofunctor 𝑃 X →
    type-polynomial-endofunctor 𝑄 X
  type-cartesian-natural-transformation-polynomial-endofunctor =
    type-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      natural-transformation-cartesian-natural-transformation-polynomial-endofunctor

  naturality-cartesian-natural-transformation-polynomial-endofunctor :
    coherence-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      ( type-cartesian-natural-transformation-polynomial-endofunctor)
  naturality-cartesian-natural-transformation-polynomial-endofunctor =
    naturality-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      natural-transformation-cartesian-natural-transformation-polynomial-endofunctor

  is-cartesian-cartesian-natural-transformation-polynomial-endofunctor :
    is-cartesian-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      natural-transformation-cartesian-natural-transformation-polynomial-endofunctor
  is-cartesian-cartesian-natural-transformation-polynomial-endofunctor = pr2 α
```

### The associated family of cartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α@(α' , H) : cartesian-natural-transformation-polynomial-endofunctor l5 𝑃 𝑄)
  where

  hom-arrow-cartesian-natural-transformation-polynomial-endofunctor :
    {X Y : UU l5} (f : X → Y) →
    hom-arrow (map-polynomial-endofunctor 𝑃 f) (map-polynomial-endofunctor 𝑄 f)
  hom-arrow-cartesian-natural-transformation-polynomial-endofunctor =
    hom-arrow-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α'

  cartesian-hom-arrow-cartesian-natural-transformation-polynomial-endofunctor :
    {X Y : UU l5} (f : X → Y) →
    cartesian-hom-arrow
      ( map-polynomial-endofunctor 𝑃 f)
      ( map-polynomial-endofunctor 𝑄 f)
  cartesian-hom-arrow-cartesian-natural-transformation-polynomial-endofunctor
    f =
    ( hom-arrow-cartesian-natural-transformation-polynomial-endofunctor f , H f)
```

### The identity cartesian natural transformation

```agda
id-cartesian-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 : Level} (𝑃 : polynomial-endofunctor l1 l2) →
  cartesian-natural-transformation-polynomial-endofunctor l3 𝑃 𝑃
pr1 (id-cartesian-natural-transformation-polynomial-endofunctor 𝑃) =
  id-natural-transformation-polynomial-endofunctor 𝑃
pr2 (id-cartesian-natural-transformation-polynomial-endofunctor 𝑃) f =
  is-cartesian-id-hom-arrow
```

### Composition of cartesian natural transformations

```agda
module _
  {l1 l2 l3 l4 l5 l6 l : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (𝑅 : polynomial-endofunctor l5 l6)
  (β@(β' , H) : cartesian-natural-transformation-polynomial-endofunctor l 𝑄 𝑅)
  (α@(α' , K) : cartesian-natural-transformation-polynomial-endofunctor l 𝑃 𝑄)
  where

  is-cartesian-comp-cartesian-natural-transformation-polynomial-endofunctor :
    is-cartesian-natural-transformation-polynomial-endofunctor 𝑃 𝑅
      ( comp-natural-transformation-polynomial-endofunctor 𝑃 𝑄 𝑅 β' α')
  is-cartesian-comp-cartesian-natural-transformation-polynomial-endofunctor f =
    is-cartesian-comp-hom-arrow
      ( map-polynomial-endofunctor 𝑃 f)
      ( map-polynomial-endofunctor 𝑄 f)
      ( map-polynomial-endofunctor 𝑅 f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor 𝑄 𝑅 β' f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α' f)
      ( H f)
      ( K f)

  comp-cartesian-natural-transformation-polynomial-endofunctor :
    cartesian-natural-transformation-polynomial-endofunctor l 𝑃 𝑅
  comp-cartesian-natural-transformation-polynomial-endofunctor =
    ( comp-natural-transformation-polynomial-endofunctor 𝑃 𝑄 𝑅 β' α' ,
      is-cartesian-comp-cartesian-natural-transformation-polynomial-endofunctor)
```
