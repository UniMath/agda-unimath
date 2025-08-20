# Fully-faithful maps

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.fully-faithful-maps
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.postcomposition-functions
open import foundation.pullbacks
open import foundation.retractions
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sections

open import orthogonal-factorization-systems.orthogonal-maps

open import simplicial-type-theory.action-on-directed-edges-functions I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.whiskering-directed-edges-identifications I
```

</details>

## Idea

A
{{#concept "simplicially fully-faithful map" Disambiguation="of simplicial types" Agda=is-fully-faithful▵}}
from one type into another is a map that induces
[equivalences](foundation-core.equivalences.md) on
[hom-types](simplicial-type-theory.directed-edges.md). In other words, the
directed edges `f x →▵ f y` for a simplicially fully-faithful map `f : A → B`
are in one-to-one correspondence with the directed edges `x →▵ y`.

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-fully-faithful▵ : (A → B) → UU (I1 ⊔ l1 ⊔ l2)
  is-fully-faithful▵ f =
    (x y : A) → is-equiv (action-hom▵-function f {x} {y})

  equiv-action-is-fully-faithful▵ :
    {f : A → B} (e : is-fully-faithful▵ f)
    {x y : A} → (x →▵ y) ≃ (f x →▵ f y)
  equiv-action-is-fully-faithful▵ {f} e {x} {y} =
    ( action-hom▵-function f , e x y)

  inv-equiv-action-is-fully-faithful▵ :
    {f : A → B} (e : is-fully-faithful▵ f)
    {x y : A} → (f x →▵ f y) ≃ (x →▵ y)
  inv-equiv-action-is-fully-faithful▵ e =
    inv-equiv (equiv-action-is-fully-faithful▵ e)

fully-faithful-map▵ : {l1 l2 : Level} → UU l1 → UU l2 → UU (I1 ⊔ l1 ⊔ l2)
fully-faithful-map▵ A B = Σ (A → B) (is-fully-faithful▵)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-fully-faithful-map▵ : fully-faithful-map▵ A B → A → B
  map-fully-faithful-map▵ = pr1

  is-fully-faithful▵-map-fully-faithful-map▵ :
    (f : fully-faithful-map▵ A B) →
    is-fully-faithful▵ (map-fully-faithful-map▵ f)
  is-fully-faithful▵-map-fully-faithful-map▵ = pr2

  equiv-action-fully-faithful-map▵ :
    (e : fully-faithful-map▵ A B) {x y : A} →
    ( x →▵ y) ≃
    ( map-fully-faithful-map▵ e x →▵
      map-fully-faithful-map▵ e y)
  equiv-action-fully-faithful-map▵ e =
    equiv-action-is-fully-faithful▵
      ( is-fully-faithful▵-map-fully-faithful-map▵ e)

  inv-equiv-action-fully-faithful-map▵ :
    (e : fully-faithful-map▵ A B)
    {x y : A} →
    ( map-fully-faithful-map▵ e x →▵
      map-fully-faithful-map▵ e y) ≃
    ( x →▵ y)
  inv-equiv-action-fully-faithful-map▵ e =
    inv-equiv (equiv-action-fully-faithful-map▵ e)
```

## Properties

### Being fully faithful is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-property-is-fully-faithful▵ :
    (f : A → B) → is-prop (is-fully-faithful▵ f)
  is-property-is-fully-faithful▵ f =
    is-prop-Π
      ( λ x →
        is-prop-Π
          ( λ y → is-property-is-equiv (action-hom▵-function f)))

  is-fully-faithful▵-Prop : (A → B) → Prop (I1 ⊔ l1 ⊔ l2)
  is-fully-faithful▵-Prop f =
    ( is-fully-faithful▵ f ,
      is-property-is-fully-faithful▵ f)
```

### The identity map is fully faithful

```agda
module _
  {l : Level} {A : UU l}
  where

  is-fully-faithful▵-id :
    is-fully-faithful▵ (id {A = A})
  is-fully-faithful▵-id x y =
    is-equiv-htpy id compute-action-hom▵-id-function is-equiv-id

  id-fully-faithful-map▵ : fully-faithful-map▵ A A
  id-fully-faithful-map▵ =
    ( id , is-fully-faithful▵-id)
```

### Equivalences are fully faithful

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-fully-faithful▵-is-equiv :
    {f : A → B} → is-equiv f → is-fully-faithful▵ f
  is-fully-faithful▵-is-equiv {f} H x y =
    is-equiv-map-Σ
      ( λ α → (α 0▵ ＝ f x) × (α 1▵ ＝ f y))
      ( is-equiv-postcomp-is-equiv f H Δ¹)
      ( λ α →
        is-equiv-map-product
          ( ap f)
          ( ap f)
          ( is-emb-is-equiv H (α 0▵) x)
          ( is-emb-is-equiv H (α 1▵) y))

  equiv-action-hom▵ :
    (e : A ≃ B) → (x y : A) → hom▵ x y ≃ hom▵ (map-equiv e x) (map-equiv e y)
  equiv-action-hom▵ e x y =
    ( action-hom▵-function (map-equiv e) ,
      is-fully-faithful▵-is-equiv (is-equiv-map-equiv e) x y)
```

### A map is fully faithful if and only if it is `(∂Δ¹ → Δ¹)`-orthogonal

> This remains to be formalized.

### To prove that a map is fully faithful, a point in the domain may be assumed

```agda
module _
  {l : Level} {A : UU l} {l2 : Level} {B : UU l2} {f : A → B}
  where

  is-fully-faithful▵-is-fully-faithful▵ :
    (A → is-fully-faithful▵ f) → is-fully-faithful▵ f
  is-fully-faithful▵-is-fully-faithful▵ H x y = H x x y
```

### fully faithful maps are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-fully-faithful▵-htpy :
      {f g : A → B} (H : f ~ g) →
      is-fully-faithful▵ g →
      is-fully-faithful▵ f
    is-fully-faithful▵-htpy {f} {g} H is-ff-g x y =
      is-equiv-top-map-triangle
        ( action-hom▵-function g)
        ( double-whisker-hom▵ (H x) (H y))
        ( action-hom▵-function f)
        ( nat-htpy▵ H)
        ( is-equiv-double-whisker-hom▵ (H x) (H y))
        ( is-ff-g x y)

  is-fully-faithful▵-htpy-fully-faithful-map▵ :
    {f : A → B} (e : fully-faithful-map▵ A B) →
    f ~ map-fully-faithful-map▵ e →
    is-fully-faithful▵ f
  is-fully-faithful▵-htpy-fully-faithful-map▵ e H =
    is-fully-faithful▵-htpy H
      ( is-fully-faithful▵-map-fully-faithful-map▵ e)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-fully-faithful▵-htpy' :
      {f g : A → B} (H : f ~ g) →
      is-fully-faithful▵ f →
      is-fully-faithful▵ g
    is-fully-faithful▵-htpy' H is-ff-f =
      is-fully-faithful▵-htpy (inv-htpy H) is-ff-f

  is-fully-faithful▵-htpy-fully-faithful-map▵' :
    (e : fully-faithful-map▵ A B) {g : A → B} →
    map-fully-faithful-map▵ e ~ g →
    is-fully-faithful▵ g
  is-fully-faithful▵-htpy-fully-faithful-map▵' e H =
    is-fully-faithful▵-htpy' H
      ( is-fully-faithful▵-map-fully-faithful-map▵ e)
```

### Any map between propositions is fully faithful

**Proof:** Propositions are simplicially discrete, so a simplicially
fully-faithful map between them is an embedding.

```text
is-fully-faithful▵-is-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-prop A → is-prop B → is-fully-faithful▵ f
is-fully-faithful▵-is-prop H K =
  is-fully-faithful▵-is-prop-map (is-trunc-map-is-trunc-domain-codomain neg-one-𝕋 H K)
```

### fully faithful maps are closed under retracts of maps

> This remains to be formalized.

### fully faithful maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-fully-faithful▵-comp :
    (g : B → C) (h : A → B) →
    is-fully-faithful▵ g →
    is-fully-faithful▵ h →
    is-fully-faithful▵ (g ∘ h)
  is-fully-faithful▵-comp g h is-ff-g is-ff-h x y =
    is-equiv-left-map-triangle
      ( action-hom▵-function (g ∘ h))
      ( action-hom▵-function g)
      ( action-hom▵-function h)
      ( compute-action-hom▵-comp-function g h)
      ( is-ff-h x y)
      ( is-ff-g (h x) (h y))

  abstract
    is-fully-faithful▵-left-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-fully-faithful▵ g →
      is-fully-faithful▵ h → is-fully-faithful▵ f
    is-fully-faithful▵-left-map-triangle f g h H is-ff-g is-ff-h =
      is-fully-faithful▵-htpy H
        ( is-fully-faithful▵-comp g h is-ff-g is-ff-h)

  comp-fully-faithful-map▵ :
    fully-faithful-map▵ B C → fully-faithful-map▵ A B → fully-faithful-map▵ A C
  comp-fully-faithful-map▵ (g , H) (f , K) =
    ( g ∘ f , is-fully-faithful▵-comp g f H K)
```

### The right factor of a fully faithful composite is fully faithful

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-fully-faithful▵-right-factor :
    (g : B → C) (h : A → B) →
    is-fully-faithful▵ g →
    is-fully-faithful▵ (g ∘ h) →
    is-fully-faithful▵ h
  is-fully-faithful▵-right-factor g h is-ff-g is-ff-gh x y =
    is-equiv-top-map-triangle
      ( action-hom▵-function (g ∘ h))
      ( action-hom▵-function g)
      ( action-hom▵-function h)
      ( compute-action-hom▵-comp-function g h)
      ( is-ff-g (h x) (h y))
      ( is-ff-gh x y)

  abstract
    is-fully-faithful▵-top-map-triangle :
      (f : A → C) (g : B → C) (h : A → B)
      (H : coherence-triangle-maps f g h) →
      is-fully-faithful▵ g →
      is-fully-faithful▵ f →
      is-fully-faithful▵ h
    is-fully-faithful▵-top-map-triangle
      f g h H is-ff-g is-ff-f x y =
      is-equiv-top-map-triangle
        ( action-hom▵-function (g ∘ h))
        ( action-hom▵-function g)
        ( action-hom▵-function h)
        ( compute-action-hom▵-comp-function g h)
        ( is-ff-g (h x) (h y))
        ( is-fully-faithful▵-htpy (inv-htpy H) is-ff-f x y)

  abstract
    is-fully-faithful▵-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e →
      is-fully-faithful▵ g →
      is-fully-faithful▵ f
    is-fully-faithful▵-triangle-is-equiv
      f g e H is-equiv-e is-ff-g =
      is-fully-faithful▵-left-map-triangle f g e H is-ff-g
        ( is-fully-faithful▵-is-equiv is-equiv-e)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-fully-faithful▵-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e →
      is-fully-faithful▵ f →
      is-fully-faithful▵ g
    is-fully-faithful▵-triangle-is-equiv'
      f g e H is-equiv-e is-ff-f =
      is-fully-faithful▵-triangle-is-equiv g f
        ( map-inv-is-equiv is-equiv-e)
        ( triangle-section f g e H
          ( pair
            ( map-inv-is-equiv is-equiv-e)
            ( is-section-map-inv-is-equiv is-equiv-e)))
        ( is-equiv-map-inv-is-equiv is-equiv-e)
        ( is-ff-f)
```

### The map on total spaces induced by a family of fully faithful maps is fully faithful

> This remains to be formalized.

### The functoriality of dependent pair types preserves fully faithful maps

> This remains to be formalized.

### Equivalence on total spaces induced by fully faithful maps on the base types

We saw above that given a fully faithful map `f : fully-faithful-map▵ A B` and a
type family `C` over `B` we obtain a fully faithful map

```text
  Σ A (C ∘ f) ↪ Σ B C.
```

This map can be upgraded to an equivalence if, furthermore, we know that the
support of `C` is contained in the image of `f`. More precisely, if we are given
a section `((b , c) : Σ B C) → fiber f b`, then it follows that

```text
  Σ A (C ∘ f) ≃ Σ B C.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  (f : fully-faithful-map▵ A B)
  (H : ((b , c) : Σ B C) → fiber (map-fully-faithful-map▵ f) b)
  where

  map-inv-Σ-fully-faithful-map▵-base :
    Σ B C → Σ A (C ∘ map-fully-faithful-map▵ f)
  pr1 (map-inv-Σ-fully-faithful-map▵-base u) = pr1 (H u)
  pr2 (map-inv-Σ-fully-faithful-map▵-base u) =
    inv-tr C (pr2 (H u)) (pr2 u)

  is-section-map-inv-Σ-fully-faithful-map▵-base :
    is-section
      ( map-Σ-map-base (map-fully-faithful-map▵ f) C)
      ( map-inv-Σ-fully-faithful-map▵-base)
  is-section-map-inv-Σ-fully-faithful-map▵-base (b , c) =
    ap
      ( λ s → (pr1 s , inv-tr C (pr2 s) c))
      ( eq-is-contr (is-torsorial-Id' b))

  -- is-retraction-map-inv-Σ-fully-faithful-map▵-base :
  --   is-retraction (map-Σ-map-base (map-fully-faithful-map▵ f) C) map-inv-Σ-fully-faithful-map▵-base
  -- is-retraction-map-inv-Σ-fully-faithful-map▵-base (a , c) =
  --   ap
  --     ( λ s → (pr1 s , inv-tr C (pr2 s) c))
  --     ( eq-is-prop (is-prop-map-is-fully-faithful▵ (pr2 f) (map-fully-faithful-map▵ f a)))

  -- equiv-Σ-fully-faithful-map▵-base : Σ A (C ∘ map-fully-faithful-map▵ f) ≃ Σ B C
  -- pr1 equiv-Σ-fully-faithful-map▵-base = map-Σ-map-base (map-fully-faithful-map▵ f) C
  -- pr2 equiv-Σ-fully-faithful-map▵-base =
  --   is-equiv-is-invertible
  --     map-inv-Σ-fully-faithful-map▵-base
  --     is-section-map-inv-Σ-fully-faithful-map▵-base
  --     is-retraction-map-inv-Σ-fully-faithful-map▵-base
```

> This remains to be formalized.

### The product of two fully faithful maps is fully faithful

> This remains to be formalized.

### Fully faithful maps are closed under pullback

> This remains to be formalized.
