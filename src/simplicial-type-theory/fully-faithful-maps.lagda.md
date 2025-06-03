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
open import simplicial-type-theory.whiskering-directed-edges I
```

</details>

## Idea

A
{{#concept "simplicially fully-faithful map" Disambiguation="of simplicial types" Agda=is-simplicially-fully-faithful}}
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

  is-simplicially-fully-faithful : (A → B) → UU (I1 ⊔ l1 ⊔ l2)
  is-simplicially-fully-faithful f =
    (x y : A) → is-equiv (action-hom▵-function f {x} {y})

  equiv-action-is-simplicially-fully-faithful :
    {f : A → B} (e : is-simplicially-fully-faithful f)
    {x y : A} → (x →▵ y) ≃ (f x →▵ f y)
  equiv-action-is-simplicially-fully-faithful {f} e {x} {y} =
    ( action-hom▵-function f , e x y)

  inv-equiv-action-is-simplicially-fully-faithful :
    {f : A → B} (e : is-simplicially-fully-faithful f)
    {x y : A} → (f x →▵ f y) ≃ (x →▵ y)
  inv-equiv-action-is-simplicially-fully-faithful e =
    inv-equiv (equiv-action-is-simplicially-fully-faithful e)

infix 5 _↪▵_
_↪▵_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (I1 ⊔ l1 ⊔ l2)
A ↪▵ B = Σ (A → B) (is-simplicially-fully-faithful)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-simplicially-fully-faithful-map : A ↪▵ B → A → B
  map-simplicially-fully-faithful-map = pr1

  is-simplicially-fully-faithful-map-simplicially-fully-faithful-map :
    (f : A ↪▵ B) →
    is-simplicially-fully-faithful (map-simplicially-fully-faithful-map f)
  is-simplicially-fully-faithful-map-simplicially-fully-faithful-map = pr2

  equiv-action-simplicially-fully-faithful-map :
    (e : A ↪▵ B) {x y : A} →
    ( x →▵ y) ≃
    ( map-simplicially-fully-faithful-map e x →▵
      map-simplicially-fully-faithful-map e y)
  equiv-action-simplicially-fully-faithful-map e =
    equiv-action-is-simplicially-fully-faithful
      ( is-simplicially-fully-faithful-map-simplicially-fully-faithful-map e)

  inv-equiv-action-simplicially-fully-faithful-map :
    (e : A ↪▵ B)
    {x y : A} →
    ( map-simplicially-fully-faithful-map e x →▵
      map-simplicially-fully-faithful-map e y) ≃
    ( x →▵ y)
  inv-equiv-action-simplicially-fully-faithful-map e =
    inv-equiv (equiv-action-simplicially-fully-faithful-map e)
```

## Properties

### Being simplicially fully faithful is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-property-is-simplicially-fully-faithful :
    (f : A → B) → is-prop (is-simplicially-fully-faithful f)
  is-property-is-simplicially-fully-faithful f =
    is-prop-Π
      ( λ x →
        is-prop-Π
          ( λ y → is-property-is-equiv (action-hom▵-function f)))

  is-simplicially-fully-faithful-Prop : (A → B) → Prop (I1 ⊔ l1 ⊔ l2)
  is-simplicially-fully-faithful-Prop f =
    ( is-simplicially-fully-faithful f ,
      is-property-is-simplicially-fully-faithful f)
```

### The identity map is simplicially fully faithful

```agda
module _
  {l : Level} {A : UU l}
  where

  is-simplicially-fully-faithful-id :
    is-simplicially-fully-faithful (id {A = A})
  is-simplicially-fully-faithful-id x y =
    is-equiv-htpy id compute-action-hom▵-id-function is-equiv-id

  id-simplicially-fully-faithful-map : A ↪▵ A
  id-simplicially-fully-faithful-map =
    ( id , is-simplicially-fully-faithful-id)
```

### Equivalences are simplicially fully faithful

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-simplicially-fully-faithful-is-equiv :
    {f : A → B} → is-equiv f → is-simplicially-fully-faithful f
  is-simplicially-fully-faithful-is-equiv {f} H x y =
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
      is-simplicially-fully-faithful-is-equiv (is-equiv-map-equiv e) x y)
```

### A map is simplicially fully faithful if and only if it is `(∂Δ¹ → Δ¹)`-orthogonal

> This remains to be formalized.

### To prove that a map is simplicially fully faithful, a point in the domain may be assumed

```agda
module _
  {l : Level} {A : UU l} {l2 : Level} {B : UU l2} {f : A → B}
  where

  is-simplicially-fully-faithful-is-simplicially-fully-faithful :
    (A → is-simplicially-fully-faithful f) → is-simplicially-fully-faithful f
  is-simplicially-fully-faithful-is-simplicially-fully-faithful H x y = H x x y
```

### Simplicially fully faithful maps are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-simplicially-fully-faithful-htpy :
      {f g : A → B} (H : f ~ g) →
      is-simplicially-fully-faithful g →
      is-simplicially-fully-faithful f
    is-simplicially-fully-faithful-htpy {f} {g} H is-ff-g x y =
      is-equiv-top-map-triangle
        ( action-hom▵-function g)
        ( double-whisker-hom▵ (H x) (H y))
        ( action-hom▵-function f)
        ( nat-htpy▵ H)
        ( is-equiv-double-whisker-hom▵ (H x) (H y))
        ( is-ff-g x y)

  is-simplicially-fully-faithful-htpy-simplicially-fully-faithful-map :
    {f : A → B} (e : A ↪▵ B) →
    f ~ map-simplicially-fully-faithful-map e →
    is-simplicially-fully-faithful f
  is-simplicially-fully-faithful-htpy-simplicially-fully-faithful-map e H =
    is-simplicially-fully-faithful-htpy H
      ( is-simplicially-fully-faithful-map-simplicially-fully-faithful-map e)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-simplicially-fully-faithful-htpy' :
      {f g : A → B} (H : f ~ g) →
      is-simplicially-fully-faithful f →
      is-simplicially-fully-faithful g
    is-simplicially-fully-faithful-htpy' H is-ff-f =
      is-simplicially-fully-faithful-htpy (inv-htpy H) is-ff-f

  is-simplicially-fully-faithful-htpy-simplicially-fully-faithful-map' :
    (e : A ↪▵ B) {g : A → B} →
    map-simplicially-fully-faithful-map e ~ g →
    is-simplicially-fully-faithful g
  is-simplicially-fully-faithful-htpy-simplicially-fully-faithful-map' e H =
    is-simplicially-fully-faithful-htpy' H
      ( is-simplicially-fully-faithful-map-simplicially-fully-faithful-map e)
```

### Any map between propositions is simplicially fully faithful

**Proof:** Propositions are simplicially discrete, so a simplicially
fully-faithful map between them is an embedding.

```text
is-simplicially-fully-faithful-is-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-prop A → is-prop B → is-simplicially-fully-faithful f
is-simplicially-fully-faithful-is-prop H K =
  is-simplicially-fully-faithful-is-prop-map (is-trunc-map-is-trunc-domain-codomain neg-one-𝕋 H K)
```

### Any map between `-1`-coskeletal types is simplicially fully faithful

> This remains to be formalized.

### Simplicially fully faithful maps are closed under retracts of maps

> This remains to be formalized.

### Simplicially fully faithful maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-simplicially-fully-faithful-comp :
    (g : B → C) (h : A → B) →
    is-simplicially-fully-faithful g →
    is-simplicially-fully-faithful h →
    is-simplicially-fully-faithful (g ∘ h)
  is-simplicially-fully-faithful-comp g h is-ff-g is-ff-h x y =
    is-equiv-left-map-triangle
      ( action-hom▵-function (g ∘ h))
      ( action-hom▵-function g)
      ( action-hom▵-function h)
      ( compute-action-hom▵-comp-function g h)
      ( is-ff-h x y)
      ( is-ff-g (h x) (h y))

  abstract
    is-simplicially-fully-faithful-left-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-simplicially-fully-faithful g →
      is-simplicially-fully-faithful h → is-simplicially-fully-faithful f
    is-simplicially-fully-faithful-left-map-triangle f g h H is-ff-g is-ff-h =
      is-simplicially-fully-faithful-htpy H
        ( is-simplicially-fully-faithful-comp g h is-ff-g is-ff-h)

  comp-simplicially-fully-faithful-map :
    (B ↪▵ C) → (A ↪▵ B) → (A ↪▵ C)
  comp-simplicially-fully-faithful-map (g , H) (f , K) =
    ( g ∘ f , is-simplicially-fully-faithful-comp g f H K)
```

### The right factor of a composed embedding is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-simplicially-fully-faithful-right-factor :
    (g : B → C) (h : A → B) →
    is-simplicially-fully-faithful g →
    is-simplicially-fully-faithful (g ∘ h) →
    is-simplicially-fully-faithful h
  is-simplicially-fully-faithful-right-factor g h is-ff-g is-ff-gh x y =
    is-equiv-top-map-triangle
      ( action-hom▵-function (g ∘ h))
      ( action-hom▵-function g)
      ( action-hom▵-function h)
      ( compute-action-hom▵-comp-function g h)
      ( is-ff-g (h x) (h y))
      ( is-ff-gh x y)

  abstract
    is-simplicially-fully-faithful-top-map-triangle :
      (f : A → C) (g : B → C) (h : A → B)
      (H : coherence-triangle-maps f g h) →
      is-simplicially-fully-faithful g →
      is-simplicially-fully-faithful f →
      is-simplicially-fully-faithful h
    is-simplicially-fully-faithful-top-map-triangle
      f g h H is-ff-g is-ff-f x y =
      is-equiv-top-map-triangle
        ( action-hom▵-function (g ∘ h))
        ( action-hom▵-function g)
        ( action-hom▵-function h)
        ( compute-action-hom▵-comp-function g h)
        ( is-ff-g (h x) (h y))
        ( is-simplicially-fully-faithful-htpy (inv-htpy H) is-ff-f x y)

  abstract
    is-simplicially-fully-faithful-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e →
      is-simplicially-fully-faithful g →
      is-simplicially-fully-faithful f
    is-simplicially-fully-faithful-triangle-is-equiv
      f g e H is-equiv-e is-ff-g =
      is-simplicially-fully-faithful-left-map-triangle f g e H is-ff-g
        ( is-simplicially-fully-faithful-is-equiv is-equiv-e)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-simplicially-fully-faithful-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e →
      is-simplicially-fully-faithful f →
      is-simplicially-fully-faithful g
    is-simplicially-fully-faithful-triangle-is-equiv'
      f g e H is-equiv-e is-ff-f =
      is-simplicially-fully-faithful-triangle-is-equiv g f
        ( map-inv-is-equiv is-equiv-e)
        ( triangle-section f g e H
          ( pair
            ( map-inv-is-equiv is-equiv-e)
            ( is-section-map-inv-is-equiv is-equiv-e)))
        ( is-equiv-map-inv-is-equiv is-equiv-e)
        ( is-ff-f)
```

### The map on total spaces induced by a family of simplicially fully faithful maps is simplicially fully faithful

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  -- is-simplicially-fully-faithful-tot :
  --   {f : (x : A) → B x → C x} → ((x : A) → is-simplicially-fully-faithful (f x)) → is-simplicially-fully-faithful (tot f)
  -- is-simplicially-fully-faithful-tot H =
  --   is-simplicially-fully-faithful-is-prop-map (is-prop-map-tot (λ x → is-prop-map-is-simplicially-fully-faithful (H x)))

  -- simplicially-fully-faithful-map-tot : ((x : A) → B x ↪▵ C x) → Σ A B ↪▵ Σ A C
  -- pr1 (simplicially-fully-faithful-map-tot f) = tot (λ x → map-simplicially-fully-faithful-map (f x))
  -- pr2 (simplicially-fully-faithful-map-tot f) = is-simplicially-fully-faithful-tot (λ x → is-simplicially-fully-faithful-map-simplicially-fully-faithful-map (f x))
```

### The functoriality of dependent pair types preserves simplicially fully faithful maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  -- abstract
  --   is-simplicially-fully-faithful-map-Σ-map-base :
  --     {f : A → B} (C : B → UU l3) → is-simplicially-fully-faithful f → is-simplicially-fully-faithful (map-Σ-map-base f C)
  --   is-simplicially-fully-faithful-map-Σ-map-base C H =
  --     is-simplicially-fully-faithful-is-prop-map (is-prop-map-map-Σ-map-base C (is-prop-map-is-simplicially-fully-faithful H))

  -- simplicially-fully-faithful-map-Σ-simplicially-fully-faithful-map-base :
  --   (f : A ↪▵ B) (C : B → UU l3) → Σ A (λ a → C (map-simplicially-fully-faithful-map f a)) ↪▵ Σ B C
  -- pr1 (simplicially-fully-faithful-map-Σ-simplicially-fully-faithful-map-base f C) = map-Σ-map-base (map-simplicially-fully-faithful-map f) C
  -- pr2 (simplicially-fully-faithful-map-Σ-simplicially-fully-faithful-map-base f C) =
  --   is-simplicially-fully-faithful-map-Σ-map-base C (is-simplicially-fully-faithful-map-simplicially-fully-faithful-map f)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  -- is-simplicially-fully-faithful-map-Σ :
  --   (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
  --   is-simplicially-fully-faithful f → ((x : A) → is-simplicially-fully-faithful (g x)) → is-simplicially-fully-faithful (map-Σ D f g)
  -- is-simplicially-fully-faithful-map-Σ D H K =
  --   is-simplicially-fully-faithful-is-prop-map
  --     ( is-prop-map-map-Σ D
  --       ( is-prop-map-is-simplicially-fully-faithful H)
  --       ( λ x → is-prop-map-is-simplicially-fully-faithful (K x)))

  -- simplicially-fully-faithful-map-Σ :
  --   (D : B → UU l4) (f : A ↪▵ B) (g : (x : A) → C x ↪▵ D (map-simplicially-fully-faithful-map f x)) →
  --   Σ A C ↪▵ Σ B D
  -- pr1 (simplicially-fully-faithful-map-Σ D f g) = map-Σ D (map-simplicially-fully-faithful-map f) (λ x → map-simplicially-fully-faithful-map (g x))
  -- pr2 (simplicially-fully-faithful-map-Σ D f g) =
  --   is-simplicially-fully-faithful-map-Σ D (is-simplicially-fully-faithful-map-simplicially-fully-faithful-map f) (λ x → is-simplicially-fully-faithful-map-simplicially-fully-faithful-map (g x))
```

### Equivalence on total spaces induced by simplicially fully faithful maps on the base types

We saw above that given an embedding `f : A ↪▵ B` and a type family `C` over `B`
we obtain an embedding

```text
  Σ A (C ∘ f) ↪▵ Σ B C.
```

This embedding can be upgraded to an equivalence if we furthermore know that the
support of `C` is contained in the image of `f`. More precisely, if we are given
a section `((b , c) : Σ B C) → fiber f b`, then it follows that

```text
  Σ A (C ∘ f) ≃ Σ B C.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} (f : A ↪▵ B)
  (H : ((b , c) : Σ B C) → fiber (map-simplicially-fully-faithful-map f) b)
  where

  map-inv-Σ-simplicially-fully-faithful-map-base :
    Σ B C → Σ A (C ∘ map-simplicially-fully-faithful-map f)
  pr1 (map-inv-Σ-simplicially-fully-faithful-map-base u) = pr1 (H u)
  pr2 (map-inv-Σ-simplicially-fully-faithful-map-base u) =
    inv-tr C (pr2 (H u)) (pr2 u)

  is-section-map-inv-Σ-simplicially-fully-faithful-map-base :
    is-section
      ( map-Σ-map-base (map-simplicially-fully-faithful-map f) C)
      ( map-inv-Σ-simplicially-fully-faithful-map-base)
  is-section-map-inv-Σ-simplicially-fully-faithful-map-base (b , c) =
    ap
      ( λ s → (pr1 s , inv-tr C (pr2 s) c))
      ( eq-is-contr (is-torsorial-Id' b))

  -- is-retraction-map-inv-Σ-simplicially-fully-faithful-map-base :
  --   is-retraction (map-Σ-map-base (map-simplicially-fully-faithful-map f) C) map-inv-Σ-simplicially-fully-faithful-map-base
  -- is-retraction-map-inv-Σ-simplicially-fully-faithful-map-base (a , c) =
  --   ap
  --     ( λ s → (pr1 s , inv-tr C (pr2 s) c))
  --     ( eq-is-prop (is-prop-map-is-simplicially-fully-faithful (pr2 f) (map-simplicially-fully-faithful-map f a)))

  -- equiv-Σ-simplicially-fully-faithful-map-base : Σ A (C ∘ map-simplicially-fully-faithful-map f) ≃ Σ B C
  -- pr1 equiv-Σ-simplicially-fully-faithful-map-base = map-Σ-map-base (map-simplicially-fully-faithful-map f) C
  -- pr2 equiv-Σ-simplicially-fully-faithful-map-base =
  --   is-equiv-is-invertible
  --     map-inv-Σ-simplicially-fully-faithful-map-base
  --     is-section-map-inv-Σ-simplicially-fully-faithful-map-base
  --     is-retraction-map-inv-Σ-simplicially-fully-faithful-map-base
```

### The product of two simplicially fully faithful maps is simplicially fully faithful

```agda
-- module _
--   {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
--   where

--   simplicially-fully-faithful-map-product : (A ↪▵ C) → (B ↪▵ D) → ((A × B) ↪▵ (C × D))
--   simplicially-fully-faithful-map-product f g = simplicially-fully-faithful-map-Σ (λ _ → D) f (λ _ → g)

--   is-simplicially-fully-faithful-map-product :
--     (f : A → C) (g : B → D) → is-simplicially-fully-faithful f → is-simplicially-fully-faithful g → (is-simplicially-fully-faithful (map-product f g))
--   is-simplicially-fully-faithful-map-product f g is-ff-f is-ff-g =
--     is-simplicially-fully-faithful-map-simplicially-fully-faithful-map (simplicially-fully-faithful-map-product (f , is-ff-f) (g , is-ff-g))
```

### Simplicially fully-faithful maps are closed under pullback

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  -- abstract
  --   is-simplicially-fully-faithful-vertical-map-cone-is-pullback :
  --     is-pullback f g c → is-simplicially-fully-faithful g → is-simplicially-fully-faithful (vertical-map-cone f g c)
  --   is-simplicially-fully-faithful-vertical-map-cone-is-pullback pb is-ff-g =
  --     is-simplicially-fully-faithful-is-prop-map
  --       ( is-trunc-vertical-map-is-pullback neg-one-𝕋 f g c pb
  --         ( is-prop-map-is-simplicially-fully-faithful is-ff-g))

  -- abstract
  --   is-simplicially-fully-faithful-horizontal-map-cone-is-pullback :
  --     is-pullback f g c → is-simplicially-fully-faithful f → is-simplicially-fully-faithful (horizontal-map-cone f g c)
  --   is-simplicially-fully-faithful-horizontal-map-cone-is-pullback pb is-ff-f =
  --     is-simplicially-fully-faithful-is-prop-map
  --       ( is-trunc-horizontal-map-is-pullback neg-one-𝕋 f g c pb
  --         ( is-prop-map-is-simplicially-fully-faithful is-ff-f))
```

### A map is an embedding if and only if it has contractible fibers at values

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  -- is-simplicially-fully-faithful-is-contr-fibers-values' :
  --   ((a : A) → is-contr (fiber' f (f a))) → is-simplicially-fully-faithful f
  -- is-simplicially-fully-faithful-is-contr-fibers-values' c a =
  --   fundamental-theorem-id (c a) (λ x → ap f {a} {x})

  -- is-simplicially-fully-faithful-is-contr-fibers-values :
  --   ((a : A) → is-contr (fiber f (f a))) → is-simplicially-fully-faithful f
  -- is-simplicially-fully-faithful-is-contr-fibers-values c =
  --   is-simplicially-fully-faithful-is-contr-fibers-values'
  --     ( λ a →
  --       is-contr-equiv'
  --         ( fiber f (f a))
  --         ( equiv-fiber f (f a))
  --         ( c a))

  -- is-contr-fibers-values-is-simplicially-fully-faithful' :
  --   is-simplicially-fully-faithful f → ((a : A) → is-contr (fiber' f (f a)))
  -- is-contr-fibers-values-is-simplicially-fully-faithful' e a =
  --   fundamental-theorem-id' (λ x → ap f {a} {x}) (e a)

  -- is-contr-fibers-values-is-simplicially-fully-faithful :
  --   is-simplicially-fully-faithful f → ((a : A) → is-contr (fiber f (f a)))
  -- is-contr-fibers-values-is-simplicially-fully-faithful e a =
  --   is-contr-equiv
  --     ( fiber' f (f a))
  --     ( equiv-fiber f (f a))
  --     ( is-contr-fibers-values-is-simplicially-fully-faithful' e a)
```
