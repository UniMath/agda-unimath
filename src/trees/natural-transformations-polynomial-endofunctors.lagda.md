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
$𝑃 ≐ (A ◃ B)$ and $𝑄 ≐ (C ◃ D)$, a
{{#concept "natural transformation" Disambiguation="of polynomial endofunctors of types" Agda=natural-transformation-polynomial-endofunctor}}
$α$ from $𝑃$ to $𝑄$ is a family of maps $α : (X : Type) → 𝑃(X) → 𝑄(X)$ such that
for every map of types $f : X → Y$, the following square commutes

```text
              𝑃(f)
     𝑃(X) -----------> 𝑃(Y)
       |                |
       |                |
  α(X) |                | α(Y)
       |                |
       ∨                ∨
     𝑄(X) -----------> 𝑄(Y).
              𝑄(f)
```

## Definitions

### Natural transformations between polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  coherence-natural-transformation-polynomial-endofunctor :
    {l : Level} →
    ( {X : UU l} →
      type-polynomial-endofunctor 𝑃 X →
      type-polynomial-endofunctor 𝑄 X) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  coherence-natural-transformation-polynomial-endofunctor {l} φ₀ =
    {X Y : UU l} (f : X → Y) →
    coherence-square-maps
      ( map-polynomial-endofunctor 𝑃 f)
      ( φ₀)
      ( φ₀)
      ( map-polynomial-endofunctor 𝑄 f)

  natural-transformation-polynomial-endofunctor :
    (l : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  natural-transformation-polynomial-endofunctor l =
    Σ ( {X : UU l} →
        type-polynomial-endofunctor 𝑃 X →
        type-polynomial-endofunctor 𝑄 X)
      ( coherence-natural-transformation-polynomial-endofunctor)

module _
  {l1 l2 l3 l4 l5 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5)
  where

  type-natural-transformation-polynomial-endofunctor :
    {X : UU l5} →
    type-polynomial-endofunctor 𝑃 X →
    type-polynomial-endofunctor 𝑄 X
  type-natural-transformation-polynomial-endofunctor = pr1 α

  naturality-natural-transformation-polynomial-endofunctor :
    coherence-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      ( type-natural-transformation-polynomial-endofunctor)
  naturality-natural-transformation-polynomial-endofunctor = pr2 α
```

### The identity natural transformation

```agda
id-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 : Level} (𝑃 : polynomial-endofunctor l1 l2) →
  natural-transformation-polynomial-endofunctor 𝑃 𝑃 l3
pr1 (id-natural-transformation-polynomial-endofunctor 𝑃) = id
pr2 (id-natural-transformation-polynomial-endofunctor 𝑃) f x = refl
```

## Properties

### Characterizing equality of natural transformations

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  htpy-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  htpy-natural-transformation-polynomial-endofunctor α β =
    Σ ( (X : UU l5) →
        type-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α {X} ~
        type-natural-transformation-polynomial-endofunctor 𝑃 𝑄 β {X})
      ( λ H →
        (X Y : UU l5) (f : X → Y) →
        coherence-square-homotopies
          ( map-polynomial-endofunctor 𝑄 f ·l H X)
          ( naturality-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α f)
          ( naturality-natural-transformation-polynomial-endofunctor 𝑃 𝑄 β f)
          ( H Y ·r map-polynomial-endofunctor 𝑃 f))

  refl-htpy-natural-transformation-polynomial-endofunctor :
    (α : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5) →
    htpy-natural-transformation-polynomial-endofunctor α α
  refl-htpy-natural-transformation-polynomial-endofunctor α =
    ( (λ X x → refl) , (λ X Y f x → right-unit))

  htpy-eq-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5) →
    (α ＝ β) → htpy-natural-transformation-polynomial-endofunctor α β
  htpy-eq-natural-transformation-polynomial-endofunctor α .α refl =
    refl-htpy-natural-transformation-polynomial-endofunctor α

  is-torsorial-htpy-natural-transformation-polynomial-endofunctor :
    (α : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5) →
    is-torsorial (htpy-natural-transformation-polynomial-endofunctor α)
  is-torsorial-htpy-natural-transformation-polynomial-endofunctor α =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-implicit-Π'
        ( λ X →
          is-torsorial-htpy
            ( type-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α))
        )
      ( type-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α ,
        ( λ _ _ → refl))
      ( is-torsorial-Eq-implicit-Π'
        ( λ X →
          is-torsorial-Eq-implicit-Π'
            ( λ Y →
              is-torsorial-Eq-Π
                ( λ f →
                  is-torsorial-htpy
                    ( ( naturality-natural-transformation-polynomial-endofunctor
                          𝑃 𝑄 α f) ∙h
                      ( refl-htpy))))))

  is-equiv-htpy-eq-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5) →
    is-equiv (htpy-eq-natural-transformation-polynomial-endofunctor α β)
  is-equiv-htpy-eq-natural-transformation-polynomial-endofunctor α =
    fundamental-theorem-id
      ( is-torsorial-htpy-natural-transformation-polynomial-endofunctor α)
      ( htpy-eq-natural-transformation-polynomial-endofunctor α)

  equiv-htpy-eq-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5) →
    (α ＝ β) ≃ htpy-natural-transformation-polynomial-endofunctor α β
  equiv-htpy-eq-natural-transformation-polynomial-endofunctor α β =
    ( htpy-eq-natural-transformation-polynomial-endofunctor α β ,
      is-equiv-htpy-eq-natural-transformation-polynomial-endofunctor α β)

  eq-htpy-natural-transformation-polynomial-endofunctor :
    (α β : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l5) →
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
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (𝑅 : polynomial-endofunctor l5 l6) →
  natural-transformation-polynomial-endofunctor 𝑄 𝑅 l →
  natural-transformation-polynomial-endofunctor 𝑃 𝑄 l →
  natural-transformation-polynomial-endofunctor 𝑃 𝑅 l
comp-natural-transformation-polynomial-endofunctor 𝑃 𝑄 𝑅 (β₀ , β₁) (α₀ , α₁) =
  ( ( β₀ ∘ α₀) ,
    ( λ f →
      pasting-vertical-coherence-square-maps
        ( map-polynomial-endofunctor 𝑃 f)
        ( α₀)
        ( α₀)
        ( map-polynomial-endofunctor 𝑄 f)
        ( β₀)
        ( β₀)
        ( map-polynomial-endofunctor 𝑅 f)
        ( α₁ f)
        ( β₁ f)))
```

### Unit laws for composition of natural transformations

```agda
left-unit-law-comp-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 l4 l : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4) →
  (α : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l) →
  ( comp-natural-transformation-polynomial-endofunctor 𝑃 𝑄 𝑄
    ( id-natural-transformation-polynomial-endofunctor 𝑄)
    ( α)) ＝
  α
left-unit-law-comp-natural-transformation-polynomial-endofunctor
  𝑃 𝑄 α@(α₀ , α₁) =
  eq-htpy-natural-transformation-polynomial-endofunctor 𝑃 𝑄
    ( comp-natural-transformation-polynomial-endofunctor 𝑃 𝑄 𝑄
      ( id-natural-transformation-polynomial-endofunctor 𝑄)
      ( α))
    ( α)
    ( ( λ X x → refl) , (λ X Y f x → right-unit ∙ ap-id (α₁ f x)))

right-unit-law-comp-natural-transformation-polynomial-endofunctor :
  {l1 l2 l3 l4 l : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4) →
  (α : natural-transformation-polynomial-endofunctor 𝑃 𝑄 l) →
  ( comp-natural-transformation-polynomial-endofunctor 𝑃 𝑃 𝑄
    ( α)
    ( id-natural-transformation-polynomial-endofunctor 𝑃)) ＝
  α
right-unit-law-comp-natural-transformation-polynomial-endofunctor
  𝑃 𝑄 α@(α₀ , α₁) =
  eq-htpy-natural-transformation-polynomial-endofunctor 𝑃 𝑄
    ( comp-natural-transformation-polynomial-endofunctor 𝑃 𝑃 𝑄
      ( α)
      ( id-natural-transformation-polynomial-endofunctor 𝑃))
    ( α)
    ( ( λ X x → refl) , (λ X Y f x → right-unit ∙ right-unit))
```

## See also

- [Morphisms of polynomial endofunctors](trees.morphisms-polynomial-endofunctors.md)
