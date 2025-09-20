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
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.morphisms-arrows
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.raising-universe-levels
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-equivalences
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
    (a : shape-polynomial-endofunctor 𝑃) →
    is-equiv (position-hom-polynomial-endofunctor 𝑃 𝑄 α a)

  is-prop-is-cartesian-hom-polynomial-endofunctor :
    is-prop is-cartesian-hom-polynomial-endofunctor
  is-prop-is-cartesian-hom-polynomial-endofunctor =
    is-prop-Π
      ( λ a →
        is-property-is-equiv (position-hom-polynomial-endofunctor 𝑃 𝑄 α a))

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
  (α₀ : shape-polynomial-endofunctor 𝑃 → shape-polynomial-endofunctor 𝑄) →
  ( (a : shape-polynomial-endofunctor 𝑃) →
    position-polynomial-endofunctor 𝑄 (α₀ a) ≃
    position-polynomial-endofunctor 𝑃 a) →
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

  shape-cartesian-hom-polynomial-endofunctor :
    shape-polynomial-endofunctor 𝑃 → shape-polynomial-endofunctor 𝑄
  shape-cartesian-hom-polynomial-endofunctor =
    shape-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor

  position-cartesian-hom-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor 𝑃) →
    position-polynomial-endofunctor 𝑄
      ( shape-hom-polynomial-endofunctor 𝑃 𝑄
        ( hom-cartesian-hom-polynomial-endofunctor)
        ( a)) →
    position-polynomial-endofunctor 𝑃 a
  position-cartesian-hom-polynomial-endofunctor =
    position-hom-polynomial-endofunctor 𝑃 𝑄
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

  equiv-position-cartesian-hom-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor 𝑃) →
    position-polynomial-endofunctor 𝑄
      ( shape-hom-polynomial-endofunctor 𝑃 𝑄
        ( hom-cartesian-hom-polynomial-endofunctor)
        ( a)) ≃
    position-polynomial-endofunctor 𝑃 a
  equiv-position-cartesian-hom-polynomial-endofunctor a =
    ( position-cartesian-hom-polynomial-endofunctor a ,
      is-cartesian-cartesian-hom-polynomial-endofunctor a)

  naturality-cartesian-hom-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    coherence-square-maps
      ( map-polynomial-endofunctor 𝑃 f)
      ( type-cartesian-hom-polynomial-endofunctor)
      ( type-cartesian-hom-polynomial-endofunctor)
      ( map-polynomial-endofunctor 𝑄 f)
  naturality-cartesian-hom-polynomial-endofunctor =
    naturality-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor

  natural-transformation-cartesian-hom-polynomial-endofunctor :
    {l : Level} → natural-transformation-polynomial-endofunctor l 𝑃 𝑄
  natural-transformation-cartesian-hom-polynomial-endofunctor =
    natural-transformation-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor

  hom-arrow-cartesian-hom-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    hom-arrow (map-polynomial-endofunctor 𝑃 f) (map-polynomial-endofunctor 𝑄 f)
  hom-arrow-cartesian-hom-polynomial-endofunctor =
    hom-arrow-hom-polynomial-endofunctor 𝑃 𝑄
      hom-cartesian-hom-polynomial-endofunctor

  cone-cartesian-hom-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    cone
      ( type-cartesian-hom-polynomial-endofunctor)
      ( map-polynomial-endofunctor 𝑄 f)
      ( type-polynomial-endofunctor 𝑃 X)
  cone-cartesian-hom-polynomial-endofunctor =
    cone-hom-polynomial-endofunctor 𝑃 𝑄 hom-cartesian-hom-polynomial-endofunctor
```

### The identity cartesian morphism

```agda
id-cartesian-hom-polynomial-endofunctor :
  {l1 l2 : Level}
  (𝑃 : polynomial-endofunctor l1 l2) →
  cartesian-hom-polynomial-endofunctor 𝑃 𝑃
id-cartesian-hom-polynomial-endofunctor 𝑃 =
  ( id-hom-polynomial-endofunctor 𝑃 , (λ a → is-equiv-id))
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
comp-cartesian-hom-polynomial-endofunctor
  𝑃 𝑄 𝑅 ((β₀ , β₁) , H) ((α₀ , α₁) , K) =
  ( ( comp-hom-polynomial-endofunctor 𝑃 𝑄 𝑅 (β₀ , β₁) (α₀ , α₁)) ,
    ( λ a → is-equiv-comp (α₁ a) (β₁ (α₀ a)) (H (α₀ a)) (K a)))
```

## Properties

### A computation of the type of cartesian morphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  cartesian-hom-polynomial-endofunctor' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cartesian-hom-polynomial-endofunctor' =
    Σ ( shape-polynomial-endofunctor 𝑃 → shape-polynomial-endofunctor 𝑄)
      ( λ α₀ →
        ((a : shape-polynomial-endofunctor 𝑃) →
          position-polynomial-endofunctor 𝑄 (α₀ a) ≃
          position-polynomial-endofunctor 𝑃 a))

  reassociate-type-cartesian-hom-polynomial-endofunctor :
    cartesian-hom-polynomial-endofunctor 𝑃 𝑄 ≃
    cartesian-hom-polynomial-endofunctor'
  reassociate-type-cartesian-hom-polynomial-endofunctor =
    ( equiv-tot (λ _ → inv-distributive-Π-Σ)) ∘e (associative-Σ _ _ _)
```

### Truncatedness of the type of cartesian morphisms

If the shapes and positions of the codomain $𝑄$ are $k$-truncated, for $k ≥ -1$,
then the type of cartesian morphisms $𝑃 → 𝑄$ is $k$-truncated.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  is-trunc-succ-cartesian-hom-polynomial-endofunctor' :
    (k : 𝕋) →
    is-trunc (succ-𝕋 k) (shape-polynomial-endofunctor 𝑄) →
    ( (c : shape-polynomial-endofunctor 𝑄) →
      is-trunc (succ-𝕋 k) (position-polynomial-endofunctor 𝑄 c)) →
    is-trunc (succ-𝕋 k) (cartesian-hom-polynomial-endofunctor' 𝑃 𝑄)
  is-trunc-succ-cartesian-hom-polynomial-endofunctor' k hQ hQ' =
    is-trunc-Σ
      ( is-trunc-function-type (succ-𝕋 k) hQ)
      ( λ f →
        is-trunc-Π
          ( succ-𝕋 k)
          ( λ e → is-trunc-equiv-is-trunc-domain k (hQ' (f e))))

  is-trunc-succ-cartesian-hom-polynomial-endofunctor :
    (k : 𝕋) →
    is-trunc (succ-𝕋 k) (shape-polynomial-endofunctor 𝑄) →
    ( (c : shape-polynomial-endofunctor 𝑄) →
      is-trunc (succ-𝕋 k) (position-polynomial-endofunctor 𝑄 c)) →
    is-trunc (succ-𝕋 k) (cartesian-hom-polynomial-endofunctor 𝑃 𝑄)
  is-trunc-succ-cartesian-hom-polynomial-endofunctor k hQ hQ' =
    is-trunc-equiv
      ( succ-𝕋 k)
      ( cartesian-hom-polynomial-endofunctor' 𝑃 𝑄)
      ( reassociate-type-cartesian-hom-polynomial-endofunctor 𝑃 𝑄)
      ( is-trunc-succ-cartesian-hom-polynomial-endofunctor' k hQ hQ')
```

### Computing the fibers of the induced natural transformation

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : cartesian-hom-polynomial-endofunctor 𝑃 𝑄)
  (let α₀ = shape-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α)
  (let α₁ = position-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α)
  {X : UU l5}
  where

  compute-fiber-type-cartesian-hom-polynomial-endofunctor :
    (c : shape-polynomial-endofunctor 𝑄)
    (x : position-polynomial-endofunctor 𝑄 c → X) →
    fiber (type-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α {X = X}) (c , x) ≃
    fiber α₀ c
  compute-fiber-type-cartesian-hom-polynomial-endofunctor c x =
    equivalence-reasoning
      fiber (type-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α {X = X}) (c , x)
      ≃ Σ ( fiber α₀ c)
          ( λ (a , p) →
            fiber
              ( precomp (α₁ a) X)
              ( inv-tr (λ c → position-polynomial-endofunctor 𝑄 c → X) p x))
        by
          compute-fiber-map-Σ
            ( λ c → position-polynomial-endofunctor 𝑄 c → X)
            ( α₀)
            ( λ a → precomp (α₁ a) X)
            ( c , x)
      ≃ fiber α₀ c
        by
          right-unit-law-Σ-is-contr
            ( λ (a , p) →
              is-contr-map-is-equiv
                ( is-equiv-precomp-is-equiv
                  ( α₁ a)
                  ( is-cartesian-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α a)
                  ( X))
                ( inv-tr (λ c → position-polynomial-endofunctor 𝑄 c → X) p x))
```

### The associated natural transformation of a cartesian morphism is cartesian

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : cartesian-hom-polynomial-endofunctor 𝑃 𝑄)
  where

  abstract
    is-cartesian-natural-transformation-cartesian-hom-polynomial-endofunctor :
      {l : Level} →
      is-cartesian-natural-transformation-polynomial-endofunctor 𝑃 𝑄
        ( natural-transformation-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α {l})
    is-cartesian-natural-transformation-cartesian-hom-polynomial-endofunctor f =
      is-pullback-is-fiberwise-equiv-map-fiber-horizontal-map-cone
        ( type-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α)
        ( map-polynomial-endofunctor 𝑄 f)
        ( cone-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α f)
        ( λ (a , y) →
          is-equiv-source-is-equiv-target-equiv-arrow
            ( map-fiber-horizontal-map-cone
              ( type-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α)
              ( map-polynomial-endofunctor 𝑄 f)
              ( cone-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α f)
              ( a , y))
            ( id)
            ( ( compute-fiber-type-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α a
                ( y)) ,
              ( compute-fiber-type-cartesian-hom-polynomial-endofunctor 𝑃 𝑄 α a
                ( f ∘ y)) ,
              ( λ where (u , refl) → refl))
            ( is-equiv-id))
```

### Equivalence between cartesian morphisms and cartesian natural transformations

This is proved in a slightly different setting as part of Lemma 2.3.3 in
{{#cite GHK22}}.

## References

{{#bibliography}}
