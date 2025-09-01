# Cartesian morphisms of polynomial endofunctors

```agda
module trees.cartesian-morphisms-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
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
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equality-dependent-pair-types
open import foundation-core.retractions
open import foundation-core.torsorial-type-families

open import trees.cartesian-natural-transformations-polynomial-endofunctors
open import trees.morphisms-polynomial-endofunctors
open import trees.natural-transformations-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

Given two [polynomial endofunctors](trees.polynomial-endofunctors.md)
$𝑃 ≐ (A ◃ B)$ and $𝑄 ≐ (C ◃ D)$, a
[morphism](trees.morphisms-polynomial-endofunctors.md) $α : 𝑃 → 𝑄$ is
{{#concept "cartesian" Disambiguation="morphism of polynomial endofunctors of types" Agda=is-cartesian-hom-polynomial-endofunctor Agda=cartesian-hom-polynomial-endofunctor}}
if the family of maps

$$α₁ : (a : A) → D (α₀ a) → B a$$

is a family of [equivalences](foundation-core.equivalences.md).

## Definitions

### The predicate of being cartesian

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : hom-polynomial-endofunctor 𝑃 𝑄)
  where

  is-cartesian-hom-polynomial-endofunctor : UU (l1 ⊔ l2 ⊔ l4)
  is-cartesian-hom-polynomial-endofunctor =
    (a : shapes-polynomial-endofunctor 𝑃) →
    is-equiv (positions-hom-polynomial-endofunctor 𝑃 𝑄 α a)

  is-prop-is-cartesian-hom-polynomial-endofunctor :
    is-prop is-cartesian-hom-polynomial-endofunctor
  is-prop-is-cartesian-hom-polynomial-endofunctor =
    is-prop-Π
      ( λ a →
        is-property-is-equiv (positions-hom-polynomial-endofunctor 𝑃 𝑄 α a))

  is-cartesian-hom-polynomial-endofunctor-Prop : Prop (l1 ⊔ l2 ⊔ l4)
  is-cartesian-hom-polynomial-endofunctor-Prop =
    ( is-cartesian-hom-polynomial-endofunctor ,
      is-prop-is-cartesian-hom-polynomial-endofunctor)
```

### The type of cartesian morphisms

```agda
cartesian-hom-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
cartesian-hom-polynomial-endofunctor 𝑃 𝑄 =
  Σ ( hom-polynomial-endofunctor 𝑃 𝑄)
    ( is-cartesian-hom-polynomial-endofunctor 𝑃 𝑄)

make-cartesian-hom-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α₀ : shapes-polynomial-endofunctor 𝑃 → shapes-polynomial-endofunctor 𝑄) →
  ( (a : shapes-polynomial-endofunctor 𝑃) →
    positions-polynomial-endofunctor 𝑄 (α₀ a) ≃
    positions-polynomial-endofunctor 𝑃 a) →
  cartesian-hom-polynomial-endofunctor 𝑃 𝑄
make-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α₀ α₁ =
  ( ( α₀ , map-equiv ∘ α₁) , is-equiv-map-equiv ∘ α₁)

module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : cartesian-hom-polynomial-endofunctor 𝑃 𝑄)
  where

  hom-cartesian-hom-polynomial-endofunctor : hom-polynomial-endofunctor 𝑃 𝑄
  hom-cartesian-hom-polynomial-endofunctor = pr1 α

  shapes-cartesian-hom-polynomial-endofunctor :
    shapes-polynomial-endofunctor 𝑃 → shapes-polynomial-endofunctor 𝑄
  shapes-cartesian-hom-polynomial-endofunctor =
    shapes-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor

  positions-cartesian-hom-polynomial-endofunctor :
    (a : shapes-polynomial-endofunctor 𝑃) →
    positions-polynomial-endofunctor 𝑄
      ( shapes-hom-polynomial-endofunctor 𝑃 𝑄
        ( hom-cartesian-hom-polynomial-endofunctor)
        ( a)) →
    positions-polynomial-endofunctor 𝑃 a
  positions-cartesian-hom-polynomial-endofunctor =
    positions-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor

  type-cartesian-hom-polynomial-endofunctor :
    {l5 : Level} {X : UU l5} →
    type-polynomial-endofunctor 𝑃 X → type-polynomial-endofunctor 𝑄 X
  type-cartesian-hom-polynomial-endofunctor =
    type-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor

  is-cartesian-cartesian-hom-polynomial-endofunctor :
    is-cartesian-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor
  is-cartesian-cartesian-hom-polynomial-endofunctor = pr2 α

  equiv-positions-cartesian-hom-polynomial-endofunctor :
    (a : shapes-polynomial-endofunctor 𝑃) →
    positions-polynomial-endofunctor 𝑄
      ( shapes-hom-polynomial-endofunctor 𝑃 𝑄
        ( hom-cartesian-hom-polynomial-endofunctor)
        ( a)) ≃
    positions-polynomial-endofunctor 𝑃 a
  equiv-positions-cartesian-hom-polynomial-endofunctor a =
    ( positions-cartesian-hom-polynomial-endofunctor a ,
      is-cartesian-cartesian-hom-polynomial-endofunctor a)
```

### The identity cartesian morphism

```agda
id-cartesian-hom-polynomial-endofunctor :
  {l1 l2 : Level}
  (𝑃 : polynomial-endofunctor l1 l2) →
  cartesian-hom-polynomial-endofunctor 𝑃 𝑃
id-cartesian-hom-polynomial-endofunctor 𝑃 =
   (id-hom-polynomial-endofunctor 𝑃 , (λ a → is-equiv-id))
```

### Composition of cartesian morphisms

```agda
comp-cartesian-hom-polynomial-endofunctor :
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (𝑅 : polynomial-endofunctor l5 l6) →
  cartesian-hom-polynomial-endofunctor 𝑄 𝑅 →
  cartesian-hom-polynomial-endofunctor 𝑃 𝑄 →
  cartesian-hom-polynomial-endofunctor 𝑃 𝑅
comp-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 𝑅 (β , H) (α , K) =
  ( comp-hom-polynomial-endofunctor 𝑃 𝑄 𝑅 β α ,
    λ a → is-equiv-comp (pr2 α a) (pr2 β (pr1 α a)) (H (pr1 α a)) (K a))
```

## Properties

### Truncatedness of the type of morphisms

If the shapes and positions of the codomain $𝑄$ are $k$-truncated, for $k ≥ -1$,
then the type of cartesian morphisms $𝑃 → 𝑄$ is $k$-truncated.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  is-trunc-succ-cartesian-hom-polynomial-endofunctor :
    (k : 𝕋) →
    is-trunc (succ-𝕋 k) (shapes-polynomial-endofunctor 𝑄) →
    ( (c : shapes-polynomial-endofunctor 𝑄) →
      is-trunc (succ-𝕋 k) (positions-polynomial-endofunctor 𝑄 c)) →
    is-trunc (succ-𝕋 k) (cartesian-hom-polynomial-endofunctor 𝑃 𝑄)
  is-trunc-succ-cartesian-hom-polynomial-endofunctor k hQ hP =
    is-trunc-equiv (succ-𝕋 k) _
      ( equiv-tot (λ _ → inv-distributive-Π-Σ) ∘e associative-Σ _ _ _)
      ( is-trunc-Σ
        ( is-trunc-function-type (succ-𝕋 k) hQ)
        ( λ f →
          is-trunc-Π
            ( succ-𝕋 k)
            ( λ e → is-trunc-equiv-is-trunc-domain k (hP (f e)))))
```

### Cartesian morphisms are cartesian natural transformations

```text
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : hom-polynomial-endofunctor 𝑃 𝑄)
  where

  is-cartesian-natural-transformation-hom-polynomial-endofunctor :
    {l : Level} →
    is-cartesian-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      ( natural-transformation-hom-polynomial-endofunctor 𝑃 𝑄 α {l})
  is-cartesian-natural-transformation-hom-polynomial-endofunctor f =
    {!   !}
```

### Cartesian natural transformations define cartesian morphisms

```text
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l2 𝑃 𝑄)
  where

  shapes-natural-transformation-polynomial-endofunctor :
    shapes-polynomial-endofunctor 𝑃 → shapes-polynomial-endofunctor 𝑄
  shapes-natural-transformation-polynomial-endofunctor a =
    pr1 (type-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α (a , id))

  positions-natural-transformation-polynomial-endofunctor :
    (a : shapes-polynomial-endofunctor 𝑃) →
    positions-polynomial-endofunctor 𝑄
      ( shapes-natural-transformation-polynomial-endofunctor a) →
    positions-polynomial-endofunctor 𝑃 a
  positions-natural-transformation-polynomial-endofunctor a =
    pr2 (type-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α (a , id))

  hom-natural-transformation-polynomial-endofunctor :
    hom-polynomial-endofunctor 𝑃 𝑄
  hom-natural-transformation-polynomial-endofunctor =
    ( shapes-natural-transformation-polynomial-endofunctor ,
      positions-natural-transformation-polynomial-endofunctor)
```

### Equivalence between cartesian morphisms and cartesian natural transformations

```text
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  is-retraction-hom-natural-transformation-polynomial-endofunctor :
    is-retraction
      ( λ α → natural-transformation-hom-polynomial-endofunctor 𝑃 𝑄 α {l2})
      ( hom-natural-transformation-polynomial-endofunctor 𝑃 𝑄)
  is-retraction-hom-natural-transformation-polynomial-endofunctor α = refl

  is-section-type-hom-natural-transformation-polynomial-endofunctor :
    (α : natural-transformation-polynomial-endofunctor l2 𝑃 𝑄)
    (X : UU l2) →
    type-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      ( natural-transformation-hom-polynomial-endofunctor 𝑃 𝑄
        ( hom-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α)) ~
    type-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α {X}
  is-section-type-hom-natural-transformation-polynomial-endofunctor
    α X (a , x) =
    inv
      ( naturality-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α x
        ( a , id))
```
