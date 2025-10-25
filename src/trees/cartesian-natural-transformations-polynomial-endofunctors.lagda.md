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
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.lifts-morphisms-arrows
open import foundation.morphisms-arrows
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.raising-universe-levels
open import foundation.sections
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universal-property-cartesian-morphisms-arrows
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equality-dependent-pair-types
open import foundation-core.retractions
open import foundation-core.torsorial-type-families

open import trees.morphisms-polynomial-endofunctors
open import trees.natural-transformations-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

Given two [polynomial endofunctors](trees.polynomial-endofunctors.md)
$P ≐ (A ◃ B)$ and $Q ≐ (C ◃ D)$, then a
[natural transformation](trees.natural-transformations-polynomial-endofunctors.md)
$α$ between them is
{{#concept "cartesian" Disambiguation="natural transformations between polynomial endofunctors of types" Agda=is-cartesian-natural-transformation-polynomial-endofunctor}}
if every naturality square

```text
              α(X)
     P(X) -----------> Q(X)
       |                |
       |                |
  P(f) |                | Q(f)
       |                |
       ∨                ∨
     P(Y) -----------> Q(Y)
              α(Y)
```

is a [pullback](foundation-core.pullbacks.md).

## Definitions

### The cartesianness predicate on natural transformations between polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l P Q)
  where

  is-cartesian-natural-transformation-polynomial-endofunctor :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  is-cartesian-natural-transformation-polynomial-endofunctor =
    {X Y : UU l} (f : X → Y) →
    is-cartesian-hom-arrow
      ( map-polynomial-endofunctor P f)
      ( map-polynomial-endofunctor Q f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor P Q α f)

  abstract
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
                    ( map-polynomial-endofunctor P f)
                    ( map-polynomial-endofunctor Q f)
                    ( hom-arrow-natural-transformation-polynomial-endofunctor P Q
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
cartesian-natural-transformation-polynomial-endofunctor l P Q =
  Σ ( natural-transformation-polynomial-endofunctor l P Q)
    ( is-cartesian-natural-transformation-polynomial-endofunctor P Q)

module _
  {l1 l2 l3 l4 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : cartesian-natural-transformation-polynomial-endofunctor l P Q)
  where

  natural-transformation-cartesian-natural-transformation-polynomial-endofunctor :
    natural-transformation-polynomial-endofunctor l P Q
  natural-transformation-cartesian-natural-transformation-polynomial-endofunctor =
    pr1 α

  map-cartesian-natural-transformation-polynomial-endofunctor :
    {X : UU l} →
    type-polynomial-endofunctor P X →
    type-polynomial-endofunctor Q X
  map-cartesian-natural-transformation-polynomial-endofunctor =
    map-natural-transformation-polynomial-endofunctor P Q
      ( natural-transformation-cartesian-natural-transformation-polynomial-endofunctor)

  naturality-cartesian-natural-transformation-polynomial-endofunctor :
    coherence-natural-transformation-polynomial-endofunctor P Q
      ( map-cartesian-natural-transformation-polynomial-endofunctor)
  naturality-cartesian-natural-transformation-polynomial-endofunctor =
    naturality-natural-transformation-polynomial-endofunctor P Q
      natural-transformation-cartesian-natural-transformation-polynomial-endofunctor

  is-cartesian-cartesian-natural-transformation-polynomial-endofunctor :
    is-cartesian-natural-transformation-polynomial-endofunctor P Q
      natural-transformation-cartesian-natural-transformation-polynomial-endofunctor
  is-cartesian-cartesian-natural-transformation-polynomial-endofunctor = pr2 α
```

### The criterion of being cartesian at terminal maps

```agda
module _
  {l1 l2 l3 l4 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l P Q)
  where

  is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor =
    {X : UU l} →
    is-cartesian-hom-arrow
      ( map-polynomial-endofunctor P (raise-terminal-map X))
      ( map-polynomial-endofunctor Q (raise-terminal-map X))
      ( hom-arrow-natural-transformation-polynomial-endofunctor P Q α
        ( raise-terminal-map X))

  is-prop-is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor :
    is-prop
      is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor
  is-prop-is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor =
    is-prop-implicit-Π
      ( λ X →
        is-prop-is-cartesian-hom-arrow
          ( map-polynomial-endofunctor P (raise-terminal-map X))
          ( map-polynomial-endofunctor Q (raise-terminal-map X))
          ( hom-arrow-natural-transformation-polynomial-endofunctor P Q α
            ( raise-terminal-map X)))

  is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor-Prop :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor-Prop =
    ( is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor ,
      is-prop-is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor)
```

### The associated family of cartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α@(α' , H) : cartesian-natural-transformation-polynomial-endofunctor l5 P Q)
  where

  hom-arrow-cartesian-natural-transformation-polynomial-endofunctor :
    {X Y : UU l5} (f : X → Y) →
    hom-arrow (map-polynomial-endofunctor P f) (map-polynomial-endofunctor Q f)
  hom-arrow-cartesian-natural-transformation-polynomial-endofunctor =
    hom-arrow-natural-transformation-polynomial-endofunctor P Q α'

  cone-cartesian-natural-transformation-polynomial-endofunctor :
    {X Y : UU l5} (f : X → Y) →
    cone
      ( map-cartesian-natural-transformation-polynomial-endofunctor P Q α)
      ( map-polynomial-endofunctor Q f)
      ( type-polynomial-endofunctor P X)
  cone-cartesian-natural-transformation-polynomial-endofunctor =
    cone-natural-transformation-polynomial-endofunctor P Q α'

  cartesian-hom-arrow-cartesian-natural-transformation-polynomial-endofunctor :
    {X Y : UU l5} (f : X → Y) →
    cartesian-hom-arrow
      ( map-polynomial-endofunctor P f)
      ( map-polynomial-endofunctor Q f)
  cartesian-hom-arrow-cartesian-natural-transformation-polynomial-endofunctor
    f =
    ( hom-arrow-cartesian-natural-transformation-polynomial-endofunctor f , H f)
```

### The associated morphism of polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : cartesian-natural-transformation-polynomial-endofunctor l2 P Q)
  (let P₀ = shape-polynomial-endofunctor P)
  (let P₁ = position-polynomial-endofunctor P)
  (let α₀ = map-cartesian-natural-transformation-polynomial-endofunctor P Q α)
  where

  shape-cartesian-natural-transformation-polynomial-endofunctor :
    shape-polynomial-endofunctor P → shape-polynomial-endofunctor Q
  shape-cartesian-natural-transformation-polynomial-endofunctor =
    shape-natural-transformation-polynomial-endofunctor P Q
      ( natural-transformation-cartesian-natural-transformation-polynomial-endofunctor
          P Q α)

  position-cartesian-natural-transformation-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor P) →
    position-polynomial-endofunctor Q
      ( shape-cartesian-natural-transformation-polynomial-endofunctor a) →
    position-polynomial-endofunctor P a
  position-cartesian-natural-transformation-polynomial-endofunctor =
    position-natural-transformation-polynomial-endofunctor P Q
      ( natural-transformation-cartesian-natural-transformation-polynomial-endofunctor
          P Q α)

  hom-cartesian-natural-transformation-polynomial-endofunctor :
    hom-polynomial-endofunctor P Q
  hom-cartesian-natural-transformation-polynomial-endofunctor =
    hom-natural-transformation-polynomial-endofunctor P Q
      ( natural-transformation-cartesian-natural-transformation-polynomial-endofunctor
          P Q α)
```

### The identity cartesian natural transformation

```agda
id-cartesian-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 : Level} (P : polynomial-endofunctor l1 l2) →
  cartesian-natural-transformation-polynomial-endofunctor l3 P P
pr1 (id-cartesian-natural-transformation-polynomial-endofunctor P) =
  id-natural-transformation-polynomial-endofunctor P
pr2 (id-cartesian-natural-transformation-polynomial-endofunctor P) f =
  is-cartesian-id-hom-arrow
```

### Composition of cartesian natural transformations

```agda
module _
  {l1 l2 l3 l4 l5 l6 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (R : polynomial-endofunctor l5 l6)
  (β@(β' , H) : cartesian-natural-transformation-polynomial-endofunctor l Q R)
  (α@(α' , K) : cartesian-natural-transformation-polynomial-endofunctor l P Q)
  where

  is-cartesian-comp-cartesian-natural-transformation-polynomial-endofunctor :
    is-cartesian-natural-transformation-polynomial-endofunctor P R
      ( comp-natural-transformation-polynomial-endofunctor P Q R β' α')
  is-cartesian-comp-cartesian-natural-transformation-polynomial-endofunctor f =
    is-cartesian-comp-hom-arrow
      ( map-polynomial-endofunctor P f)
      ( map-polynomial-endofunctor Q f)
      ( map-polynomial-endofunctor R f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor Q R β' f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor P Q α' f)
      ( H f)
      ( K f)

  comp-cartesian-natural-transformation-polynomial-endofunctor :
    cartesian-natural-transformation-polynomial-endofunctor l P R
  comp-cartesian-natural-transformation-polynomial-endofunctor =
    ( comp-natural-transformation-polynomial-endofunctor P Q R β' α' ,
      is-cartesian-comp-cartesian-natural-transformation-polynomial-endofunctor)
```

### A natural transformation into a polynomial endofunctor with a set of shapes is cartesian if and only if it is cartesian at terminal maps

**Proof.** One direction is trivial. For the other direction, given a natural
transformation of polynomial endofunctors $α : P ⇒ Q$ and an arbitrary function
$f : X → Y$, since the type of shapes of $Q$ is a set, the following prism
commutes and we have a morphism of arrows in the slice above $α_{*}$:

```text
         αX
  PX -----------> QX   →
   \ ⌟ →   PY ---- \ ----> QY
    \     / ⌟   αY  \     /
     \   /           \   /
      ∨ ∨             ∨ ∨
       P* -----------> Q*
              α*
```

and so by the right-cancellation property of cartesian squares the naturality
square at $f$ is cartesian. ∎

This holds more generally for coherent natural transformations between arbitrary
polynomial functors, as mentioned in Remark 2.1.4 in {{#cite GHK22}}.

```agda
module _
  {l1 l2 l3 l4 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l P Q)
  where

  is-cartesian-is-cartesian-at-terminal-map-natural-transformation-is-set-shape-polynomial-endofunctor :
    is-set (shape-polynomial-endofunctor Q) →
    is-cartesian-at-terminal-map-natural-transformation-polynomial-endofunctor
      P Q α →
    is-cartesian-natural-transformation-polynomial-endofunctor P Q α
  is-cartesian-is-cartesian-at-terminal-map-natural-transformation-is-set-shape-polynomial-endofunctor
    HQ Hα {X} {Y} f =
    is-pullback-top-square-vertical-triangle
      ( map-natural-transformation-polynomial-endofunctor P Q α)
      (map-polynomial-endofunctor Q (raise-terminal-map Y))
      (map-polynomial-endofunctor Q f)
      (map-polynomial-endofunctor Q (raise-terminal-map X))
      ( cone-natural-transformation-polynomial-endofunctor P Q α
        ( raise-terminal-map Y))
      ( cone-natural-transformation-polynomial-endofunctor P Q α f)
      ( cone-natural-transformation-polynomial-endofunctor P Q α
        ( raise-terminal-map X))
      ( refl-htpy)
      ( refl-htpy ,
        refl-htpy ,
        λ x →
        eq-is-prop
          ( is-set-Σ HQ (λ _ → is-set-function-type is-set-raise-unit) _ _))
      ( Hα {Y})
      ( Hα {X})
```

## References

{{#bibliography}}
