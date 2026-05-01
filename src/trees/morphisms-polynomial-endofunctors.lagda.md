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
open import foundation.commuting-triangles-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-truncated-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.morphisms-arrows
open import foundation.precomposition-functions
open import foundation.retracts-of-types
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
`P ≐ (A \mathbin{◃} B)` and `Q ≐ (C \mathbin{◃} D)`, a
{{#concept "morphism" Disambiguation="of polynomial endofunctors of types" Agda=hom-polynomial-endofunctor}}
`α` from `P` to `Q` consists of a pair of maps

```text
  α₀ : A → C
  α₁ : (a : A) → D (α₀ a) → B a.
```

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
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : hom-polynomial-endofunctor P Q)
  where

  shape-hom-polynomial-endofunctor :
    shape-polynomial-endofunctor P → shape-polynomial-endofunctor Q
  shape-hom-polynomial-endofunctor = pr1 α

  position-hom-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor P) →
    position-polynomial-endofunctor Q (shape-hom-polynomial-endofunctor a) →
    position-polynomial-endofunctor P a
  position-hom-polynomial-endofunctor = pr2 α

  type-hom-polynomial-endofunctor :
    {l3 : Level} {X : UU l3} →
    type-polynomial-endofunctor P X →
    type-polynomial-endofunctor Q X
  type-hom-polynomial-endofunctor {X = X} =
    map-Σ
      ( λ c → position-polynomial-endofunctor Q c → X)
      ( shape-hom-polynomial-endofunctor)
      ( λ a → precomp (position-hom-polynomial-endofunctor a) X)
```

### The identity morphism

```agda
id-hom-polynomial-endofunctor :
  {l1 l2 : Level}
  (P : polynomial-endofunctor l1 l2) →
  hom-polynomial-endofunctor P P
id-hom-polynomial-endofunctor P = (id , (λ a → id))
```

### Composition of morphisms

```agda
comp-hom-polynomial-endofunctor :
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (R : polynomial-endofunctor l5 l6) →
  hom-polynomial-endofunctor Q R →
  hom-polynomial-endofunctor P Q →
  hom-polynomial-endofunctor P R
comp-hom-polynomial-endofunctor P Q R (β₀ , β₁) (α₀ , α₁) =
  ( β₀ ∘ α₀ , (λ a → α₁ a ∘ β₁ (α₀ a)))
```

## Properties

### Characterizing equality of morphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  where

  htpy-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor P Q) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-polynomial-endofunctor α β =
    Σ ( shape-hom-polynomial-endofunctor P Q α ~
        shape-hom-polynomial-endofunctor P Q β)
      ( λ H →
        (a : shape-polynomial-endofunctor P)
        (d :
          position-polynomial-endofunctor Q
            ( shape-hom-polynomial-endofunctor P Q α a)) →
        position-hom-polynomial-endofunctor P Q α a d ＝
        position-hom-polynomial-endofunctor P Q β a
          ( tr (position-polynomial-endofunctor Q) (H a) d))

  refl-htpy-hom-polynomial-endofunctor :
    (α : hom-polynomial-endofunctor P Q) → htpy-hom-polynomial-endofunctor α α
  refl-htpy-hom-polynomial-endofunctor α = (refl-htpy , λ a d → refl)

  htpy-eq-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor P Q) →
    (α ＝ β) → htpy-hom-polynomial-endofunctor α β
  htpy-eq-hom-polynomial-endofunctor α .α refl =
    refl-htpy-hom-polynomial-endofunctor α

  abstract
    is-torsorial-htpy-hom-polynomial-endofunctor :
      (α : hom-polynomial-endofunctor P Q) →
      is-torsorial (htpy-hom-polynomial-endofunctor α)
    is-torsorial-htpy-hom-polynomial-endofunctor α =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (shape-hom-polynomial-endofunctor P Q α))
        ( shape-hom-polynomial-endofunctor P Q α , refl-htpy)
        ( is-torsorial-binary-htpy (position-hom-polynomial-endofunctor P Q α))

  abstract
    is-equiv-htpy-eq-hom-polynomial-endofunctor :
      (α β : hom-polynomial-endofunctor P Q) →
      is-equiv (htpy-eq-hom-polynomial-endofunctor α β)
    is-equiv-htpy-eq-hom-polynomial-endofunctor α =
      fundamental-theorem-id
        ( is-torsorial-htpy-hom-polynomial-endofunctor α)
        ( htpy-eq-hom-polynomial-endofunctor α)

  equiv-htpy-eq-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor P Q) →
    (α ＝ β) ≃ htpy-hom-polynomial-endofunctor α β
  equiv-htpy-eq-hom-polynomial-endofunctor α β =
    ( htpy-eq-hom-polynomial-endofunctor α β ,
      is-equiv-htpy-eq-hom-polynomial-endofunctor α β)

  eq-htpy-hom-polynomial-endofunctor :
    (α β : hom-polynomial-endofunctor P Q) →
    htpy-hom-polynomial-endofunctor α β →
    α ＝ β
  eq-htpy-hom-polynomial-endofunctor α β =
    map-inv-equiv (equiv-htpy-eq-hom-polynomial-endofunctor α β)
```

### Truncatedness of the type of morphisms

If the shapes of $Q$ and the positions of $P$ are $k$-truncated then the type of
morphisms $P → Q$ is $k$-truncated.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  where

  abstract
    is-trunc-hom-polynomial-endofunctor :
      (k : 𝕋) →
      is-trunc k (shape-polynomial-endofunctor Q) →
      ( (a : shape-polynomial-endofunctor P) →
        is-trunc k (position-polynomial-endofunctor P a)) →
      is-trunc k (hom-polynomial-endofunctor P Q)
    is-trunc-hom-polynomial-endofunctor k hQ hP =
      is-trunc-Σ
        ( is-trunc-function-type k hQ)
        ( λ f → is-trunc-Π k (λ a → is-trunc-function-type k (hP a)))
```

### Morphisms are natural transformations

Morphisms of polynomial endofunctors define
[natural transformations](trees.natural-transformations-polynomial-endofunctors.md).

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : hom-polynomial-endofunctor P Q)
  where

  naturality-hom-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    coherence-square-maps
      ( map-polynomial-endofunctor P f)
      ( type-hom-polynomial-endofunctor P Q α)
      ( type-hom-polynomial-endofunctor P Q α)
      ( map-polynomial-endofunctor Q f)
  naturality-hom-polynomial-endofunctor f = refl-htpy

  natural-transformation-hom-polynomial-endofunctor :
    {l : Level} → natural-transformation-polynomial-endofunctor l P Q
  natural-transformation-hom-polynomial-endofunctor =
    ( type-hom-polynomial-endofunctor P Q α ,
      naturality-hom-polynomial-endofunctor)

  hom-arrow-hom-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    hom-arrow (map-polynomial-endofunctor P f) (map-polynomial-endofunctor Q f)
  hom-arrow-hom-polynomial-endofunctor f =
    ( type-hom-polynomial-endofunctor P Q α ,
      type-hom-polynomial-endofunctor P Q α ,
      naturality-hom-polynomial-endofunctor f)

  cone-hom-polynomial-endofunctor :
    {l5 l6 : Level} {X : UU l5} {Y : UU l6} (f : X → Y) →
    cone
      ( type-hom-polynomial-endofunctor P Q α)
      ( map-polynomial-endofunctor Q f)
      ( type-polynomial-endofunctor P X)
  cone-hom-polynomial-endofunctor f =
    cone-hom-arrow
      ( map-polynomial-endofunctor P f)
      ( map-polynomial-endofunctor Q f)
      ( hom-arrow-hom-polynomial-endofunctor f)
```

### Natural transformations define morphisms

Given a natural transformation `α : P ⇒ Q` then we have an associated morphism
given on shapes by `a ↦ pr1 (α₀ {P₁ a} (a , id)) : P₀ → Q₀` and on positions by
`a ↦ pr2 (α₀ {P₁ a} (a , id)) : (a : P₀) → Q₁ _ → P₁ a`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α : natural-transformation-polynomial-endofunctor l2 P Q)
  where

  shape-natural-transformation-polynomial-endofunctor :
    shape-polynomial-endofunctor P → shape-polynomial-endofunctor Q
  shape-natural-transformation-polynomial-endofunctor a =
    pr1 (map-natural-transformation-polynomial-endofunctor P Q α (a , id))

  position-natural-transformation-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor P) →
    position-polynomial-endofunctor Q
      ( shape-natural-transformation-polynomial-endofunctor a) →
    position-polynomial-endofunctor P a
  position-natural-transformation-polynomial-endofunctor a =
    pr2 (map-natural-transformation-polynomial-endofunctor P Q α (a , id))

  hom-natural-transformation-polynomial-endofunctor :
    hom-polynomial-endofunctor P Q
  hom-natural-transformation-polynomial-endofunctor =
    ( shape-natural-transformation-polynomial-endofunctor ,
      position-natural-transformation-polynomial-endofunctor)
```

### Computing the fibers of the induced natural transformation

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  (α@(α₀ , α₁) : hom-polynomial-endofunctor P Q)
  (let P₁ = position-polynomial-endofunctor P)
  (let Q₀ = shape-polynomial-endofunctor Q)
  (let Q₁ = position-polynomial-endofunctor Q)
  {X : UU l5}
  where

  fiber-type-hom-polynomial-endofunctor :
    (c : Q₀) (x : Q₁ c → X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  fiber-type-hom-polynomial-endofunctor c x =
    Σ ( fiber α₀ c)
      ( λ (a , p) →
        Σ (P₁ a → X) (λ x' → coherence-square-maps (tr Q₁ p) (α₁ a) x x'))

  compute-fiber-type-hom-polynomial-endofunctor :
    (q@(c , x) : type-polynomial-endofunctor Q X) →
    fiber (type-hom-polynomial-endofunctor P Q α) q ≃
    fiber-type-hom-polynomial-endofunctor c x
  compute-fiber-type-hom-polynomial-endofunctor q@(c , x) =
    equivalence-reasoning
      fiber (type-hom-polynomial-endofunctor P Q α {X = X}) q
      ≃ Σ ( fiber α₀ c)
          ( λ (a , p) →
            fiber
              ( precomp (α₁ a) X)
              ( inv-tr (λ c' → Q₁ c' → X) p x))
        by
        compute-fiber-map-Σ
          ( λ c → position-polynomial-endofunctor Q c → X)
          ( α₀)
          ( λ a → precomp (α₁ a) X)
          ( q)
      ≃ Σ ( fiber α₀ c)
          ( λ (a , p) →
            Σ (P₁ a → X)
              (λ x' →
                coherence-triangle-maps'
                  ( inv-tr (λ c' → Q₁ c' → X) p x)
                  ( x')
                  ( α₁ a)))
        by
        equiv-tot
          ( λ (a , p) →
            compute-extension-fiber-precomp'
              ( α₁ a)
              ( inv-tr (λ c' → Q₁ c' → X) p x))
      ≃ Σ ( fiber α₀ c)
          ( λ (a , p) →
            Σ (P₁ a → X) (λ x' → coherence-square-maps (tr Q₁ p) (α₁ a) x x'))
        by
        equiv-tot
          ( λ (a , p) →
            equiv-tot
              ( λ x' →
                equiv-tr
                  ( λ u → coherence-triangle-maps' u x' (α₁ a))
                  ( ( tr-function-type-fixed-codomain Q₁ X (inv p) x) ∙
                    ( ap (λ q → x ∘ tr Q₁ q) (inv-inv p)))))
```

### Comparison between morphisms and natural transformations

Morphisms of polynomial endofunctors form a
[retract](foundation.retracts-of-types.md) of natural transformations, and this
map is a [section](foundation-core.sections.md) on shapes.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : polynomial-endofunctor l1 l2)
  (Q : polynomial-endofunctor l3 l4)
  where

  is-retraction-hom-natural-transformation-polynomial-endofunctor :
    is-retraction
      ( λ α → natural-transformation-hom-polynomial-endofunctor P Q α {l2})
      ( hom-natural-transformation-polynomial-endofunctor P Q)
  is-retraction-hom-natural-transformation-polynomial-endofunctor α = refl

  is-section-type-hom-natural-transformation-polynomial-endofunctor :
    (α : natural-transformation-polynomial-endofunctor l2 P Q)
    (X : UU l2) →
    map-natural-transformation-polynomial-endofunctor P Q
      ( natural-transformation-hom-polynomial-endofunctor P Q
        ( hom-natural-transformation-polynomial-endofunctor P Q α)) ~
    map-natural-transformation-polynomial-endofunctor P Q α {X}
  is-section-type-hom-natural-transformation-polynomial-endofunctor
    α X (a , x) =
    inv
      ( naturality-natural-transformation-polynomial-endofunctor P Q α x
        ( a , id))

  retract-hom-natural-transformation-polynomial-endofunctor :
    ( hom-polynomial-endofunctor P Q) retract-of
    ( natural-transformation-polynomial-endofunctor l2 P Q)
  retract-hom-natural-transformation-polynomial-endofunctor =
    ( λ f → natural-transformation-hom-polynomial-endofunctor P Q f {l2}) ,
    ( hom-natural-transformation-polynomial-endofunctor P Q) ,
    ( is-retraction-hom-natural-transformation-polynomial-endofunctor)
```

**Comment.** If these notions were to be equivalent we would have needed natural
transformations to satisfy the following equality:

$$
  α₁ (f ∘ x) (a , id) = ap (Q f) (α₁ x (a , id)) ∙ α₁ f (a , x),
$$

which is an instance of the unfolded condition that the naturality square of a
composite map is given by pasting of squares.
