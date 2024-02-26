# Precomposition of functions

```agda
module foundation.precomposition-functions where

open import foundation-core.precomposition-functions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.precomposition-dependent-functions
open import foundation.sections
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
```

</details>

## Idea

Given a function `f : A → B` and a type `X`, the **precomposition function** by
`f`

```text
  - ∘ f : (B → X) → (A → X)
```

is defined by `λ h x → h (f x)`.

The precomposition function was already defined in
[`foundation-core.precomposition-functions`](foundation-core.precomposition-functions.md).
In this file we derive some further properties of the precomposition function.

## Properties

### Precomposition preserves homotopies

```agda
htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : f ~ g) (C : UU l3) →
  precomp f C ~ precomp g C
htpy-precomp H C h = eq-htpy (h ·l H)

compute-htpy-precomp-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  htpy-precomp (refl-htpy' f) C ~ refl-htpy
compute-htpy-precomp-refl-htpy f C h = eq-htpy-refl-htpy (h ∘ f)
```

### Precomposition preserves concatenation of homotopies

```agda
compute-concat-htpy-precomp :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  { f g h : A → B} (H : f ~ g) (K : g ~ h) (C : UU l3) →
  htpy-precomp (H ∙h K) C ~ htpy-precomp H C ∙h htpy-precomp K C
compute-concat-htpy-precomp H K C k =
  ( ap
    ( eq-htpy)
    ( eq-htpy (distributive-left-whisker-comp-concat k H K))) ∙
  ( eq-htpy-concat-htpy (k ·l H) (k ·l K))
```

### If precomposition `- ∘ f : (Y → X) → (X → X)` has a section, then `f` has a retraction

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  retraction-section-precomp-domain : section (precomp f X) → retraction f
  pr1 (retraction-section-precomp-domain s) =
    map-section (precomp f X) s id
  pr2 (retraction-section-precomp-domain s) =
    htpy-eq (is-section-map-section (precomp f X) s id)
```

### Equivalences induce an equivalence from the type of homotopies between two maps to the type of homotopies between their precomposites

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-htpy-precomp-htpy :
    (f g : B → C) (e : A ≃ B) → (f ~ g) ≃ (f ∘ map-equiv e ~ g ∘ map-equiv e)
  equiv-htpy-precomp-htpy f g e =
    equiv-htpy-precomp-htpy-Π f g e
```

### Computations of the fibers of `precomp`

The fiber of `- ∘ f : (B → X) → (A → X)` at `g ∘ f : B → X` is equivalent to the
type of maps `h : B → X` equipped with a homotopy witnessing that the square

```text
        f
    A -----> B
    |        |
  f |        | h
    V        V
    B -----> X
        g
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  compute-coherence-triangle-fiber-precomp' :
    (g : A → X) →
    fiber (precomp f X) g ≃ Σ (B → X) (λ h → coherence-triangle-maps' g h f)
  compute-coherence-triangle-fiber-precomp' g = equiv-tot (λ _ → equiv-funext)

  compute-coherence-triangle-fiber-precomp :
    (g : A → X) →
    fiber (precomp f X) g ≃ Σ (B → X) (λ h → coherence-triangle-maps g h f)
  compute-coherence-triangle-fiber-precomp g =
    equiv-tot (λ _ → equiv-funext) ∘e equiv-fiber (precomp f X) g

  compute-fiber-precomp :
    (g : B → X) →
    fiber (precomp f X) (g ∘ f) ≃
    Σ (B → X) (λ h → coherence-square-maps f f h g)
  compute-fiber-precomp g = compute-coherence-triangle-fiber-precomp (g ∘ f)

  compute-total-fiber-precomp :
    Σ (B → X) (λ g → fiber (precomp f X) (g ∘ f)) ≃
    Σ (B → X) (λ u → Σ (B → X) (λ v → u ∘ f ~ v ∘ f))
  compute-total-fiber-precomp = equiv-tot compute-fiber-precomp

  diagonal-into-fibers-precomp :
    (B → X) → Σ (B → X) (λ g → fiber (precomp f X) (g ∘ f))
  diagonal-into-fibers-precomp = map-section-family (λ g → g , refl)
```

### The action on identifications of precomposition by a map

Consider a map `f : A → B` and two functions `g h : B → C`. Then the
[action on identifications](foundation.action-on-identifications-functions.md)
of `precomp f C` fits in a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                     ap (precomp f C)
       (g = h) --------------------------> (g ∘ f = h ∘ f)
          |                                       |
  htpy-eq |                                       | htpy-eq
          ∨                                       ∨
       (g ~ h) --------------------------> (g ∘ f ~ h ∘ f).
                precomp f (eq-value g h)
```

Similarly, the action on identifications of `precomp f C` also fits in a
commuting square

```text
                precomp f (eq-value g h)
       (g ~ h) --------------------------> (g ∘ f ~ h ∘ f)
          |                                       |
  eq-htpy |                                       | eq-htpy
          ∨                                       ∨
       (g = h) --------------------------> (g ∘ f = h ∘ f).
                     ap (precomp f C)
```

commutes.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : A → B) {g h : B → C}
  where

  compute-htpy-eq-ap-precomp :
    coherence-square-maps
      ( ap (precomp f C))
      ( htpy-eq)
      ( htpy-eq)
      ( precomp-Π f (eq-value g h))
  compute-htpy-eq-ap-precomp =
    compute-htpy-eq-ap-precomp-Π f

  compute-eq-htpy-ap-precomp :
    coherence-square-maps
      ( precomp-Π f (eq-value g h))
      ( eq-htpy)
      ( eq-htpy)
      ( ap (precomp f C))
  compute-eq-htpy-ap-precomp =
    vertical-inv-equiv-coherence-square-maps
      ( ap (precomp f C))
      ( equiv-funext)
      ( equiv-funext)
      ( precomp-Π f (eq-value g h))
      ( compute-htpy-eq-ap-precomp)
```
