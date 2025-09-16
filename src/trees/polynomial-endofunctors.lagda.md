# Polynomial endofunctors

```agda
module trees.polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.retractions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given a type `A` [equipped](foundation.structure.md) with a type family `B` over
`A`, the
{{#concept "polynomial endofunctor" WD="polynomial functor" WDID=Q48842893 Agda=polynomial-endofunctor}}
`𝑃 A B` is defined by

```text
  X ↦ Σ (x : A), (B x → X).
```

Polynomial endofunctors are important in the study of
[W-types](trees.w-types.md), and also in the study of
[combinatorial species](species.md).

## Definitions

### The type of polynomial endofunctors

```agda
polynomial-endofunctor : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
polynomial-endofunctor l1 l2 = Σ (UU l1) (λ A → (A → UU l2))

module _
  {l1 l2 : Level} (𝑃 : polynomial-endofunctor l1 l2)
  where

  shape-polynomial-endofunctor : UU l1
  shape-polynomial-endofunctor = pr1 𝑃

  position-polynomial-endofunctor : shape-polynomial-endofunctor → UU l2
  position-polynomial-endofunctor = pr2 𝑃

make-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → polynomial-endofunctor l1 l2
make-polynomial-endofunctor B = (_ , B)
```

### The action on types of a polynomial endofunctor

```agda
type-polynomial-endofunctor' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (X : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor' A B X = Σ A (λ x → B x → X)

type-polynomial-endofunctor :
  {l1 l2 l3 : Level} → polynomial-endofunctor l1 l2 → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor (A , B) = type-polynomial-endofunctor' A B
```

### The action on maps of the polynomial endofunctor

```agda
map-polynomial-endofunctor' :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  type-polynomial-endofunctor' A B X → type-polynomial-endofunctor' A B Y
map-polynomial-endofunctor' A B f = tot (λ x α → f ∘ α)

map-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (𝑃 : polynomial-endofunctor l1 l2)
  {X : UU l3} {Y : UU l4} (f : X → Y) →
  type-polynomial-endofunctor 𝑃 X → type-polynomial-endofunctor 𝑃 Y
map-polynomial-endofunctor (A , B) = map-polynomial-endofunctor' A B
```

## Properties

### Characterizing identity in the image of polynomial endofunctors

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3}
  where

  Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor' A B X) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-type-polynomial-endofunctor x y =
    Σ (pr1 x ＝ pr1 y) (λ p → coherence-triangle-maps (pr2 x) (pr2 y) (tr B p))

  refl-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor' A B X) →
    Eq-type-polynomial-endofunctor x x
  refl-Eq-type-polynomial-endofunctor (x , α) = (refl , refl-htpy)

  Eq-eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor' A B X) →
    x ＝ y → Eq-type-polynomial-endofunctor x y
  Eq-eq-type-polynomial-endofunctor x .x refl =
    refl-Eq-type-polynomial-endofunctor x

  is-torsorial-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor' A B X) →
    is-torsorial (Eq-type-polynomial-endofunctor x)
  is-torsorial-Eq-type-polynomial-endofunctor (x , α) =
    is-torsorial-Eq-structure
      ( is-torsorial-Id x)
      ( x , refl)
      ( is-torsorial-htpy α)

  is-equiv-Eq-eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor' A B X) →
    is-equiv (Eq-eq-type-polynomial-endofunctor x y)
  is-equiv-Eq-eq-type-polynomial-endofunctor x =
    fundamental-theorem-id
      ( is-torsorial-Eq-type-polynomial-endofunctor x)
      ( Eq-eq-type-polynomial-endofunctor x)

  eq-Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor' A B X) →
    Eq-type-polynomial-endofunctor x y → x ＝ y
  eq-Eq-type-polynomial-endofunctor x y =
    map-inv-is-equiv (is-equiv-Eq-eq-type-polynomial-endofunctor x y)

  is-retraction-eq-Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor' A B X) →
    is-retraction
      ( Eq-eq-type-polynomial-endofunctor x y)
      ( eq-Eq-type-polynomial-endofunctor x y)
  is-retraction-eq-Eq-type-polynomial-endofunctor x y =
    is-retraction-map-inv-is-equiv
      ( is-equiv-Eq-eq-type-polynomial-endofunctor x y)

  coh-refl-eq-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor' A B X) →
    ( eq-Eq-type-polynomial-endofunctor x x
      ( refl-Eq-type-polynomial-endofunctor x)) ＝ refl
  coh-refl-eq-Eq-type-polynomial-endofunctor x =
    is-retraction-eq-Eq-type-polynomial-endofunctor x x refl
```

### The action on homotopies of the polynomial endofunctor

```agda
htpy-polynomial-endofunctor' :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  {f g : X → Y} →
  f ~ g → map-polynomial-endofunctor' A B f ~ map-polynomial-endofunctor' A B g
htpy-polynomial-endofunctor' A B {f = f} {g} H (x , α) =
  eq-Eq-type-polynomial-endofunctor
    ( map-polynomial-endofunctor' A B f (x , α))
    ( map-polynomial-endofunctor' A B g (x , α))
    ( refl , H ·r α)

htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (𝑃 : polynomial-endofunctor l1 l2)
  {X : UU l3} {Y : UU l4} {f g : X → Y} →
  f ~ g → map-polynomial-endofunctor 𝑃 f ~ map-polynomial-endofunctor 𝑃 g
htpy-polynomial-endofunctor (A , B) = htpy-polynomial-endofunctor' A B

coh-refl-htpy-polynomial-endofunctor' :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  {X : UU l3} {Y : UU l4} (f : X → Y) →
  htpy-polynomial-endofunctor' A B (refl-htpy' f) ~ refl-htpy
coh-refl-htpy-polynomial-endofunctor' A B f (x , α) =
  coh-refl-eq-Eq-type-polynomial-endofunctor
    ( map-polynomial-endofunctor' A B f (x , α))

coh-refl-htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (𝑃 : polynomial-endofunctor l1 l2)
  {X : UU l3} {Y : UU l4} (f : X → Y) →
  htpy-polynomial-endofunctor 𝑃 (refl-htpy' f) ~ refl-htpy
coh-refl-htpy-polynomial-endofunctor (A , B) =
  coh-refl-htpy-polynomial-endofunctor' A B
```

### Computing the fibers of the action on maps

```agda
module _
  {l1 l2 l3 l4 : Level} (𝑃 : polynomial-endofunctor l1 l2)
  {X : UU l3} {Y : UU l4} (f : X → Y)
  where

  compute-fiber-map-polynomial-endofunctor :
    (a : shape-polynomial-endofunctor 𝑃)
    (y : position-polynomial-endofunctor 𝑃 a → Y) →
    fiber (map-polynomial-endofunctor 𝑃 f) (a , y) ≃
    ( (b : position-polynomial-endofunctor 𝑃 a) → fiber f (y b))
  compute-fiber-map-polynomial-endofunctor a y =
    equivalence-reasoning
    fiber (map-polynomial-endofunctor 𝑃 f) (a , y)
    ≃ fiber (postcomp (position-polynomial-endofunctor 𝑃 a) f) y
      by
        compute-fiber-tot
          ( λ a → postcomp (position-polynomial-endofunctor 𝑃 a) f)
          ( a , y)
    ≃ ((b : position-polynomial-endofunctor 𝑃 a) → fiber f (y b))
      by inv-compute-Π-fiber-postcomp (position-polynomial-endofunctor 𝑃 a) f y
```

## See also

- [Multivariable polynomial functors](trees.multivariable-polynomial-functors.md)
  for the generalization of polynomial endofunctors to type families.
- [Cauchy series of species of types](species.cauchy-series-species-of-types.md)
  are polynomial endofunctors of the form
  ```text
    X ↦ Σ (U : Type), S(U) × (U → X)
  ```
  In other words, given a [species of types](species.species-of-types.md) `S`,
  the shapes are types equipped with `S`-structure, and the positions are
  points.
- Via [type duality](foundation.type-duality.md), polynomial endofunctors are
  classified by maps of types.
