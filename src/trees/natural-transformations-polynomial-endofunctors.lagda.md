# Natural transformations between polynomial endofunctors

```agda
module trees.natural-transformations-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
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
open import foundation.morphisms-arrows
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equality-dependent-pair-types
open import foundation-core.retractions
open import foundation-core.torsorial-type-families

open import trees.polynomial-endofunctors
```

</details>

## Idea

Given two [polynomial endofunctors](trees.polynomial-endofunctors.md)
$P ≐ (A \mathbin{◃} B)$ and $Q ≐ (C \mathbin{◃} D)$, a
{{#concept "natural transformation" Disambiguation="of polynomial endofunctors of types" Agda=natural-transformation-polynomial-endofunctor}}
$α$ from $P$ to $Q$ is a family of maps $α : (X : Type) → P(X) → Q(X)$ such that
for every map of types $f : X → Y$, the following square commutes

```text
              α(X)
     P(X) -----------> Q(X)
       |                |
       |                |
  P(f) |                | Q(f)
       |                |
       ∨                ∨
     P(Y) -----------> Q(Y).
              α(Y)
```

## Definitions

### Natural transformations between polynomial endofunctors

```agda
coherence-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 l4 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4) →
  ( {X : UU l} →
    type-polynomial-endofunctor P X →
    type-polynomial-endofunctor Q X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
coherence-natural-transformation-polynomial-endofunctor {l = l} P Q α₀ =
  {X Y : UU l} (f : X → Y) →
  coherence-square-maps
    ( α₀)
    ( map-polynomial-endofunctor P f)
    ( map-polynomial-endofunctor Q f)
    ( α₀)

natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (l : Level) →
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
natural-transformation-polynomial-endofunctor l P Q =
  Σ ( {X : UU l} →
      type-polynomial-endofunctor P X →
      type-polynomial-endofunctor Q X)
    ( coherence-natural-transformation-polynomial-endofunctor P Q)

module _
  {l1 l2 l3 l4 l5 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l5 P Q)
  where

  map-natural-transformation-polynomial-endofunctor :
    {X : UU l5} →
    type-polynomial-endofunctor P X →
    type-polynomial-endofunctor Q X
  map-natural-transformation-polynomial-endofunctor = pr1 α

  naturality-natural-transformation-polynomial-endofunctor :
    coherence-natural-transformation-polynomial-endofunctor P Q
      ( map-natural-transformation-polynomial-endofunctor)
  naturality-natural-transformation-polynomial-endofunctor = pr2 α
```

### The associated family of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l5 P Q)
  (let α₀ = map-natural-transformation-polynomial-endofunctor P Q α)
  (let α₁ = naturality-natural-transformation-polynomial-endofunctor P Q α)
  {X Y : UU l5} (f : X → Y)
  where

  hom-arrow-natural-transformation-polynomial-endofunctor :
    hom-arrow (map-polynomial-endofunctor P f) (map-polynomial-endofunctor Q f)
  hom-arrow-natural-transformation-polynomial-endofunctor =
    ( α₀ , α₀ , α₁ f)

  transpose-hom-arrow-natural-transformation-polynomial-endofunctor :
    hom-arrow (α₀ {X}) (α₀ {Y})
  transpose-hom-arrow-natural-transformation-polynomial-endofunctor =
    transpose-hom-arrow
      ( map-polynomial-endofunctor P f)
      ( map-polynomial-endofunctor Q f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor)

  cone-natural-transformation-polynomial-endofunctor :
    cone α₀ (map-polynomial-endofunctor Q f) (type-polynomial-endofunctor P X)
  cone-natural-transformation-polynomial-endofunctor =
    cone-hom-arrow
      ( map-polynomial-endofunctor P f)
      ( map-polynomial-endofunctor Q f)
      ( hom-arrow-natural-transformation-polynomial-endofunctor)
```

### The identity natural transformation

```agda
id-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 : Level} (P : polynomial-endofunctor l1 l2) →
  natural-transformation-polynomial-endofunctor l3 P P
pr1 (id-natural-transformation-polynomial-endofunctor P) = id
pr2 (id-natural-transformation-polynomial-endofunctor P) f x = refl
```

## Properties

### Characterizing equality of natural transformations

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  where

  htpy-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor l5 P Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  htpy-natural-transformation-polynomial-endofunctor α β =
    Σ ( (X : UU l5) →
        map-natural-transformation-polynomial-endofunctor P Q α {X} ~
        map-natural-transformation-polynomial-endofunctor P Q β {X})
      ( λ H →
        (X Y : UU l5) (f : X → Y) →
        coherence-square-homotopies
          ( naturality-natural-transformation-polynomial-endofunctor P Q α f)
          ( H Y ·r map-polynomial-endofunctor P f)
          ( map-polynomial-endofunctor Q f ·l H X)
          ( naturality-natural-transformation-polynomial-endofunctor P Q β f))

  refl-htpy-natural-transformation-polynomial-endofunctor :
    (α : natural-transformation-polynomial-endofunctor l5 P Q) →
    htpy-natural-transformation-polynomial-endofunctor α α
  refl-htpy-natural-transformation-polynomial-endofunctor α =
    ( (λ X x → refl) , (λ X Y f x → inv right-unit))

  htpy-eq-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor l5 P Q) →
    (α ＝ β) → htpy-natural-transformation-polynomial-endofunctor α β
  htpy-eq-natural-transformation-polynomial-endofunctor α .α refl =
    refl-htpy-natural-transformation-polynomial-endofunctor α

  abstract
    is-torsorial-htpy-natural-transformation-polynomial-endofunctor :
      (α : natural-transformation-polynomial-endofunctor l5 P Q) →
      is-torsorial (htpy-natural-transformation-polynomial-endofunctor α)
    is-torsorial-htpy-natural-transformation-polynomial-endofunctor α =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-implicit-Π'
          ( λ X →
            is-torsorial-htpy
              ( map-natural-transformation-polynomial-endofunctor P Q α)))
        ( map-natural-transformation-polynomial-endofunctor P Q α ,
          ( λ _ _ → refl))
        ( is-torsorial-Eq-implicit-Π'
          ( λ X →
            is-torsorial-Eq-implicit-Π'
              ( λ Y →
                is-torsorial-Eq-Π
                  ( λ f →
                    is-torsorial-htpy'
                      ( ( naturality-natural-transformation-polynomial-endofunctor
                            P Q α f) ∙h
                        ( refl-htpy))))))

  abstract
    is-equiv-htpy-eq-natural-transformation-polynomial-endofunctor :
      (α β : natural-transformation-polynomial-endofunctor l5 P Q) →
      is-equiv (htpy-eq-natural-transformation-polynomial-endofunctor α β)
    is-equiv-htpy-eq-natural-transformation-polynomial-endofunctor α =
      fundamental-theorem-id
        ( is-torsorial-htpy-natural-transformation-polynomial-endofunctor α)
        ( htpy-eq-natural-transformation-polynomial-endofunctor α)

  equiv-htpy-eq-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor l5 P Q) →
    (α ＝ β) ≃ htpy-natural-transformation-polynomial-endofunctor α β
  equiv-htpy-eq-natural-transformation-polynomial-endofunctor α β =
    ( htpy-eq-natural-transformation-polynomial-endofunctor α β ,
      is-equiv-htpy-eq-natural-transformation-polynomial-endofunctor α β)

  eq-htpy-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor l5 P Q) →
    htpy-natural-transformation-polynomial-endofunctor α β →
    α ＝ β
  eq-htpy-natural-transformation-polynomial-endofunctor α β =
    map-inv-equiv
      ( equiv-htpy-eq-natural-transformation-polynomial-endofunctor α β)
```

### Composition of natural transformations

```agda
comp-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 l4 l5 l6 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (R : polynomial-endofunctor l5 l6) →
  natural-transformation-polynomial-endofunctor l Q R →
  natural-transformation-polynomial-endofunctor l P Q →
  natural-transformation-polynomial-endofunctor l P R
comp-natural-transformation-polynomial-endofunctor P Q R (β₀ , β₁) (α₀ , α₁) =
  ( ( β₀ ∘ α₀) ,
    ( λ f →
      pasting-horizontal-coherence-square-maps
        ( α₀)
        ( β₀)
        ( map-polynomial-endofunctor P f)
        ( map-polynomial-endofunctor Q f)
        ( map-polynomial-endofunctor R f)
        ( α₀)
        ( β₀)
        ( α₁ f)
        ( β₁ f)))
```

### Unit laws for composition of natural transformations

```agda
module _
  {l1 l2 l3 l4 l : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α@(α₀ , α₁) : natural-transformation-polynomial-endofunctor l P Q)
  where

  htpy-left-unit-law-comp-natural-transformation-polynomial-endofunctor :
    htpy-natural-transformation-polynomial-endofunctor P Q
      ( comp-natural-transformation-polynomial-endofunctor P Q Q
        ( id-natural-transformation-polynomial-endofunctor Q)
        ( α))
      ( α)
  htpy-left-unit-law-comp-natural-transformation-polynomial-endofunctor =
      ( ( λ X x → refl) ,
        ( λ X Y f x → inv (right-unit ∙ right-unit ∙ ap-id (α₁ f x))))

  left-unit-law-comp-natural-transformation-polynomial-endofunctor :
    ( comp-natural-transformation-polynomial-endofunctor P Q Q
      ( id-natural-transformation-polynomial-endofunctor Q)
      ( α)) ＝
    ( α)
  left-unit-law-comp-natural-transformation-polynomial-endofunctor =
    eq-htpy-natural-transformation-polynomial-endofunctor P Q
      ( comp-natural-transformation-polynomial-endofunctor P Q Q
        ( id-natural-transformation-polynomial-endofunctor Q)
        ( α))
      ( α)
      ( htpy-left-unit-law-comp-natural-transformation-polynomial-endofunctor)

  htpy-right-unit-law-comp-natural-transformation-polynomial-endofunctor :
    htpy-natural-transformation-polynomial-endofunctor P Q
      ( comp-natural-transformation-polynomial-endofunctor P P Q
        ( α)
        ( id-natural-transformation-polynomial-endofunctor P))
      ( α)
  htpy-right-unit-law-comp-natural-transformation-polynomial-endofunctor =
      ( ( λ X x → refl) , (λ X Y f x → inv right-unit))

  right-unit-law-comp-natural-transformation-polynomial-endofunctor :
    ( comp-natural-transformation-polynomial-endofunctor P P Q
      ( α)
      ( id-natural-transformation-polynomial-endofunctor P)) ＝
    ( α)
  right-unit-law-comp-natural-transformation-polynomial-endofunctor =
    eq-htpy-natural-transformation-polynomial-endofunctor P Q
      ( comp-natural-transformation-polynomial-endofunctor P P Q
        ( α)
        ( id-natural-transformation-polynomial-endofunctor P))
      ( α)
      ( htpy-right-unit-law-comp-natural-transformation-polynomial-endofunctor)
```

## See also

- [Morphisms of polynomial endofunctors](trees.morphisms-polynomial-endofunctors.md)
