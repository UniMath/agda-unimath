# Morphisms of polynomial endofunctors

```agda
module trees.morphisms-polynomial-endofunctors where
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
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
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
$𝑃 ≐ (A ◃ B)$ and $𝑄 ≐ (C ◃ D)$, a
{{#concept "morphism" Disambiguation="of polynomial endofunctors of types" Agda=hom-polynomial-endofunctor}}
$α$ from $𝑃$ to $𝑄$ consists of a map $α₀ : A → C$ and a family of maps
$$α₁ : (a : A) → D (α₀ a) → B a.$$

## Definitions

### Morphisms of polynomial endofunctors

```agda
hom-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} →
  polynomial-endofunctor l1 l2 →
  polynomial-endofunctor l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-polynomial-endofunctor (A , B) (C , D) =
  Σ (A → C) (λ α₀ → ((a : A) → D (α₀ a) → B a))

module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : hom-polynomial-endofunctor 𝑃 𝑄)
  where

  shapes-hom-polynomial-endofunctor :
    shapes-polynomial-endofunctor 𝑃 → shapes-polynomial-endofunctor 𝑄
  shapes-hom-polynomial-endofunctor = pr1 α

  positions-hom-polynomial-endofunctor :
    (a : shapes-polynomial-endofunctor 𝑃) →
    positions-polynomial-endofunctor 𝑄 (shapes-hom-polynomial-endofunctor a) →
    positions-polynomial-endofunctor 𝑃 a
  positions-hom-polynomial-endofunctor = pr2 α

  type-hom-polynomial-endofunctor :
    {l3 : Level} {X : UU l3} →
    type-polynomial-endofunctor 𝑃 X →
    type-polynomial-endofunctor 𝑄 X
  type-hom-polynomial-endofunctor {X = X} =
    map-Σ
      ( λ c → positions-polynomial-endofunctor 𝑄 c → X)
      ( shapes-hom-polynomial-endofunctor)
      ( λ a → precomp (positions-hom-polynomial-endofunctor a) X)
```

## Properties

### Characterizing equality of morphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  htpy-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor 𝑃 𝑄) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-polynomial-endofunctor α β =
    Σ ( shapes-hom-polynomial-endofunctor 𝑃 𝑄 α ~
        shapes-hom-polynomial-endofunctor 𝑃 𝑄 β)
      ( λ H →
        (a : shapes-polynomial-endofunctor 𝑃)
        (d :
          positions-polynomial-endofunctor 𝑄
            ( shapes-hom-polynomial-endofunctor 𝑃 𝑄 α a)) →
        positions-hom-polynomial-endofunctor 𝑃 𝑄 α a d ＝
        positions-hom-polynomial-endofunctor 𝑃 𝑄 β a
          ( tr (positions-polynomial-endofunctor 𝑄) (H a) d))

  refl-htpy-hom-polynomial-endofunctor :
    (α : hom-polynomial-endofunctor 𝑃 𝑄) → htpy-hom-polynomial-endofunctor α α
  refl-htpy-hom-polynomial-endofunctor α = (refl-htpy , λ a d → refl)

  htpy-eq-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor 𝑃 𝑄) →
    (α ＝ β) → htpy-hom-polynomial-endofunctor α β
  htpy-eq-hom-polynomial-endofunctor α .α refl =
    refl-htpy-hom-polynomial-endofunctor α

  is-torsorial-htpy-hom-polynomial-endofunctor :
    (α : hom-polynomial-endofunctor 𝑃 𝑄) →
    is-torsorial (htpy-hom-polynomial-endofunctor α)
  is-torsorial-htpy-hom-polynomial-endofunctor α =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (shapes-hom-polynomial-endofunctor 𝑃 𝑄 α))
      ( shapes-hom-polynomial-endofunctor 𝑃 𝑄 α , refl-htpy)
      ( is-torsorial-binary-htpy (positions-hom-polynomial-endofunctor 𝑃 𝑄 α))

  is-equiv-htpy-eq-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor 𝑃 𝑄) →
    is-equiv (htpy-eq-hom-polynomial-endofunctor α β)
  is-equiv-htpy-eq-hom-polynomial-endofunctor α =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-polynomial-endofunctor α)
      ( htpy-eq-hom-polynomial-endofunctor α)

  equiv-htpy-eq-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor 𝑃 𝑄) →
    (α ＝ β) ≃ htpy-hom-polynomial-endofunctor α β
  equiv-htpy-eq-hom-polynomial-endofunctor α β =
    ( htpy-eq-hom-polynomial-endofunctor α β ,
      is-equiv-htpy-eq-hom-polynomial-endofunctor α β)

  eq-htpy-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor 𝑃 𝑄) →
    htpy-hom-polynomial-endofunctor α β →
    α ＝ β
  eq-htpy-hom-polynomial-endofunctor α β =
    map-inv-equiv (equiv-htpy-eq-hom-polynomial-endofunctor α β)
```

### Truncatedness of the type of morphisms

If the shapes of $𝑄$ and the positions of $𝑃$ are $k$-truncated then the type of
morphisms $𝑃 → 𝑄$ is $k$-truncated.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  where

  is-trunc-hom-polynomial-endofunctor :
    (k : 𝕋) →
    is-trunc k (shapes-polynomial-endofunctor 𝑄) →
    ( (a : shapes-polynomial-endofunctor 𝑃) →
      is-trunc k (positions-polynomial-endofunctor 𝑃 a)) →
    is-trunc k (hom-polynomial-endofunctor 𝑃 𝑄)
  is-trunc-hom-polynomial-endofunctor k hQ hP =
    is-trunc-Σ
      ( is-trunc-function-type k hQ)
      ( λ f → is-trunc-Π k (λ a → is-trunc-function-type k (hP a)))
```

### Morphisms are natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : hom-polynomial-endofunctor 𝑃 𝑄)
  where

  naturality-hom-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    coherence-square-maps
      ( map-polynomial-endofunctor 𝑃 f)
      ( type-hom-polynomial-endofunctor 𝑃 𝑄 α)
      ( type-hom-polynomial-endofunctor 𝑃 𝑄 α)
      ( map-polynomial-endofunctor 𝑄 f)
  naturality-hom-polynomial-endofunctor f = refl-htpy

  natural-transformation-hom-polynomial-endofunctor :
    {l : Level} → natural-transformation-polynomial-endofunctor l 𝑃 𝑄
  natural-transformation-hom-polynomial-endofunctor =
    ( type-hom-polynomial-endofunctor 𝑃 𝑄 α ,
      naturality-hom-polynomial-endofunctor)
```

### Natural transformations define morphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝑃 : polynomial-endofunctor l1 l2)
  (𝑄 : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l2 𝑃 𝑄)
  where

  shapes-natural-transformation-polynomial-endofunctor :
    shapes-polynomial-endofunctor 𝑃 →
    shapes-polynomial-endofunctor 𝑄
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

### Equivalence between morphisms and natural transformations

```agda
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

Finally, we need to show the following equality:

$$
  α₁ (f ∘ x) (a , id) = ap (𝑄 f) (α₁ x (a , id)) ∙ α₁ f (a , x)
$$

```text
module _
  {l : Level}
  (𝑃 : polynomial-endofunctor l l)
  (𝑄 : polynomial-endofunctor l l)
  where

  is-section-is-set-positions-hom-natural-transformation-polynomial-endofunctor :
    is-section
      ( λ α → natural-transformation-hom-polynomial-endofunctor 𝑃 𝑄 α {l})
      ( hom-natural-transformation-polynomial-endofunctor 𝑃 𝑄)
  is-section-is-set-positions-hom-natural-transformation-polynomial-endofunctor α =
    eq-htpy-natural-transformation-polynomial-endofunctor 𝑃 𝑄
      ( natural-transformation-hom-polynomial-endofunctor 𝑃 𝑄
        ( hom-natural-transformation-polynomial-endofunctor 𝑃 𝑄 α))
      ( α)
      ( ( is-section-type-hom-natural-transformation-polynomial-endofunctor 𝑃 𝑄
          ( α)) ,
        ?)
```
