# Univalent polynomial endofunctors

```agda
module trees.univalent-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.univalent-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.retractions
open import foundation-core.torsorial-type-families

open import trees.polynomial-endofunctors
```

</details>

## Idea

A [polynomial endofunctor](trees.polynomial-endofunctors.md) `𝑃` is
{{#concept "univalent" Disambiguation="polynomial endofunctor" Agda=is-univalent-polynomial-endofunctor Agda=univalent-polynomial-endofunctor}}
if its type family of positions is
[univalent](foundation.univalent-type-families.md). In other words, a polynomial
endofunctor is univalent if it is equivalent to the polynomial endofunctor given
by a [subuniverse](foundation.subuniverses.md)

```text
  𝑃 ≃ (𝒮 ◃ pr1).
```

## Definitions

### The predicate on polynomial endofunctors of being univalent

```agda
is-univalent-polynomial-endofunctor :
  {l1 l2 : Level} → polynomial-endofunctor l1 l2 → UU (l1 ⊔ l2)
is-univalent-polynomial-endofunctor (A , B) = is-univalent B

is-prop-is-univalent-polynomial-endofunctor :
  {l1 l2 : Level} (𝑃 : polynomial-endofunctor l1 l2) →
  is-prop (is-univalent-polynomial-endofunctor 𝑃)
is-prop-is-univalent-polynomial-endofunctor 𝑃 = is-prop-is-univalent

is-univalent-polynomial-endofunctor-Prop :
  {l1 l2 : Level} → polynomial-endofunctor l1 l2 → Prop (l1 ⊔ l2)
is-univalent-polynomial-endofunctor-Prop 𝑃 =
  ( is-univalent-polynomial-endofunctor 𝑃 ,
    is-prop-is-univalent-polynomial-endofunctor 𝑃)
```

### The type of univalent polynomial endofunctors

```agda
univalent-polynomial-endofunctor : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
univalent-polynomial-endofunctor l1 l2 =
  Σ (polynomial-endofunctor l1 l2) (is-univalent-polynomial-endofunctor)

module _
  {l1 l2 : Level} (𝑃 : univalent-polynomial-endofunctor l1 l2)
  where

  polynomial-endofunctor-univalent-polynomial-endofunctor :
    polynomial-endofunctor l1 l2
  polynomial-endofunctor-univalent-polynomial-endofunctor = pr1 𝑃

  shapes-univalent-polynomial-endofunctor : UU l1
  shapes-univalent-polynomial-endofunctor =
    shape-polynomial-endofunctor
      polynomial-endofunctor-univalent-polynomial-endofunctor

  positions-univalent-polynomial-endofunctor :
    shapes-univalent-polynomial-endofunctor → UU l2
  positions-univalent-polynomial-endofunctor =
    position-polynomial-endofunctor
      polynomial-endofunctor-univalent-polynomial-endofunctor

  is-univalent-univalent-polynomial-endofunctor :
    is-univalent-polynomial-endofunctor
      polynomial-endofunctor-univalent-polynomial-endofunctor
  is-univalent-univalent-polynomial-endofunctor = pr2 𝑃

  univalent-family-univalent-polynomial-endofunctor :
    univalent-family l2 shapes-univalent-polynomial-endofunctor
  univalent-family-univalent-polynomial-endofunctor =
    ( positions-univalent-polynomial-endofunctor ,
      is-univalent-univalent-polynomial-endofunctor)

  equiv-equiv-tr-univalent-polynomial-endofunctor :
    {x y : shapes-univalent-polynomial-endofunctor} →
    ( x ＝ y) ≃
    ( positions-univalent-polynomial-endofunctor x ≃
      positions-univalent-polynomial-endofunctor y)
  equiv-equiv-tr-univalent-polynomial-endofunctor =
    equiv-equiv-tr-univalent-family
      univalent-family-univalent-polynomial-endofunctor

make-univalent-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-univalent B →
  univalent-polynomial-endofunctor l1 l2
make-univalent-polynomial-endofunctor B H = ((_ , B) , H)
```

### The underlying subuniverse of a univalent polynomial endofunctor

```agda
module _
  {l1 l2 : Level} (𝑃 : univalent-polynomial-endofunctor l1 l2)
  where

  subuniverse-univalent-polynomial-endofunctor :
    (l3 : Level) → subuniverse l3 (l1 ⊔ l2 ⊔ l3)
  subuniverse-univalent-polynomial-endofunctor =
    subuniverse-univalent-family
      ( univalent-family-univalent-polynomial-endofunctor 𝑃)

  is-in-subuniverse-univalent-polynomial-endofunctor :
    {l3 : Level} → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-in-subuniverse-univalent-polynomial-endofunctor {l3} =
    is-in-subuniverse (subuniverse-univalent-polynomial-endofunctor l3)

  global-subuniverse-univalent-polynomial-endofunctor :
    global-subuniverse (λ l3 → l1 ⊔ l2 ⊔ l3)
  global-subuniverse-univalent-polynomial-endofunctor =
    global-subuniverse-univalent-family
      ( univalent-family-univalent-polynomial-endofunctor 𝑃)
```

### The action on types of a univalent polynomial endofunctor

```agda
type-univalent-polynomial-endofunctor :
  {l1 l2 l3 : Level} →
  univalent-polynomial-endofunctor l1 l2 →
  UU l3 → UU (l1 ⊔ l2 ⊔ l3)
type-univalent-polynomial-endofunctor 𝑃 =
  type-polynomial-endofunctor
    ( polynomial-endofunctor-univalent-polynomial-endofunctor 𝑃)
```

### The action on maps of a univalent polynomial endofunctor

```agda
map-univalent-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (𝑃 : univalent-polynomial-endofunctor l1 l2)
  {X : UU l3} {Y : UU l4} (f : X → Y) →
  type-univalent-polynomial-endofunctor 𝑃 X →
  type-univalent-polynomial-endofunctor 𝑃 Y
map-univalent-polynomial-endofunctor 𝑃 =
  map-polynomial-endofunctor
    ( polynomial-endofunctor-univalent-polynomial-endofunctor 𝑃)
```

### Characterizing identity in the image of univalent polynomial endofunctors

```agda
module _
  {l1 l2 l3 : Level} (𝑃 : univalent-polynomial-endofunctor l1 l2) {X : UU l3}
  where

  Eq-type-univalent-polynomial-endofunctor :
    (x y : type-univalent-polynomial-endofunctor 𝑃 X) → UU (l2 ⊔ l3)
  Eq-type-univalent-polynomial-endofunctor x y =
    Σ ( positions-univalent-polynomial-endofunctor 𝑃 (pr1 x) ≃
        positions-univalent-polynomial-endofunctor 𝑃 (pr1 y))
      ( λ e → coherence-triangle-maps (pr2 x) (pr2 y) (map-equiv e))

  refl-Eq-type-univalent-polynomial-endofunctor :
    (x : type-univalent-polynomial-endofunctor 𝑃 X) →
    Eq-type-univalent-polynomial-endofunctor x x
  refl-Eq-type-univalent-polynomial-endofunctor (x , α) = (id-equiv , refl-htpy)

  Eq-eq-type-univalent-polynomial-endofunctor :
    (x y : type-univalent-polynomial-endofunctor 𝑃 X) →
    x ＝ y → Eq-type-univalent-polynomial-endofunctor x y
  Eq-eq-type-univalent-polynomial-endofunctor x .x refl =
    refl-Eq-type-univalent-polynomial-endofunctor x

  abstract
    is-torsorial-Eq-type-univalent-polynomial-endofunctor :
      (x : type-univalent-polynomial-endofunctor 𝑃 X) →
      is-torsorial (Eq-type-univalent-polynomial-endofunctor x)
    is-torsorial-Eq-type-univalent-polynomial-endofunctor (x , α) =
      is-torsorial-Eq-structure
        ( is-contr-equiv'
          ( Σ (shapes-univalent-polynomial-endofunctor 𝑃) (x ＝_))
          ( equiv-tot
            ( λ y → equiv-equiv-tr-univalent-polynomial-endofunctor 𝑃 {x} {y}))
          ( is-torsorial-Id x))
        ( x , id-equiv)
        ( is-torsorial-htpy α)

  is-equiv-Eq-eq-type-univalent-polynomial-endofunctor :
    (x y : type-univalent-polynomial-endofunctor 𝑃 X) →
    is-equiv (Eq-eq-type-univalent-polynomial-endofunctor x y)
  is-equiv-Eq-eq-type-univalent-polynomial-endofunctor x =
    fundamental-theorem-id
      ( is-torsorial-Eq-type-univalent-polynomial-endofunctor x)
      ( Eq-eq-type-univalent-polynomial-endofunctor x)

  extensionality-type-univalent-polynomial-endofunctor :
    (x y : type-univalent-polynomial-endofunctor 𝑃 X) →
    (x ＝ y) ≃ Eq-type-univalent-polynomial-endofunctor x y
  extensionality-type-univalent-polynomial-endofunctor x y =
    ( Eq-eq-type-univalent-polynomial-endofunctor x y ,
      is-equiv-Eq-eq-type-univalent-polynomial-endofunctor x y)

  eq-Eq-type-univalent-polynomial-endofunctor :
    (x y : type-univalent-polynomial-endofunctor 𝑃 X) →
    Eq-type-univalent-polynomial-endofunctor x y → x ＝ y
  eq-Eq-type-univalent-polynomial-endofunctor x y =
    map-inv-equiv (extensionality-type-univalent-polynomial-endofunctor x y)

  is-retraction-eq-Eq-type-univalent-polynomial-endofunctor :
    (x y : type-univalent-polynomial-endofunctor 𝑃 X) →
    is-retraction
      ( Eq-eq-type-univalent-polynomial-endofunctor x y)
      ( eq-Eq-type-univalent-polynomial-endofunctor x y)
  is-retraction-eq-Eq-type-univalent-polynomial-endofunctor x y =
    is-retraction-map-inv-is-equiv
      ( is-equiv-Eq-eq-type-univalent-polynomial-endofunctor x y)

  coh-refl-eq-Eq-type-univalent-polynomial-endofunctor :
    (x : type-univalent-polynomial-endofunctor 𝑃 X) →
    ( eq-Eq-type-univalent-polynomial-endofunctor x x
      ( refl-Eq-type-univalent-polynomial-endofunctor x)) ＝ refl
  coh-refl-eq-Eq-type-univalent-polynomial-endofunctor x =
    is-retraction-eq-Eq-type-univalent-polynomial-endofunctor x x refl
```

### Local smallness of the image of univalent endofunctors

```agda
module _
  {l1 l2 l3 : Level} (𝑃 : univalent-polynomial-endofunctor l1 l2) {X : UU l3}
  where

  is-locally-small-type-univalent-polynomial-endofunctor :
    is-locally-small (l2 ⊔ l3) (type-univalent-polynomial-endofunctor 𝑃 X)
  is-locally-small-type-univalent-polynomial-endofunctor x y =
    ( Eq-type-univalent-polynomial-endofunctor 𝑃 x y ,
      extensionality-type-univalent-polynomial-endofunctor 𝑃 x y)
```
