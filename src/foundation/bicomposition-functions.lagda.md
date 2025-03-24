# Bicomposition of functions

```agda
open import foundation.function-extensionality-axiom

module foundation.bicomposition-functions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext
open import foundation.postcomposition-dependent-functions funext
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps funext
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types funext
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

Given functions `f : A → B` and `g : X → Y` the
{{#concept "bicomposition function" Disambiguation="types" Agda=bicomp}} is the
map

```text
  g ∘ - ∘ f : (B → X) → (A → Y)
```

defined by `λ h x → g (h (f x))`.

## Definitions

### The bicomposition operation on ordinary functions

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (f : A → B)
  {X : UU l3} {Y : UU l4} (g : X → Y)
  where

  bicomp : (B → X) → (A → Y)
  bicomp h = g ∘ h ∘ f
```

### Bicomposition preserves homotopies

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {f f' : A → B} (F : f ~ f')
  {X : UU l3} {Y : UU l4} {g g' : X → Y} (G : g ~ g')
  where

  htpy-bicomp : bicomp f g ~ bicomp f' g'
  htpy-bicomp h = eq-htpy (G ·r (h ∘ f) ∙h (g' ∘ h) ·l F)
```

## See also

- [Composition algebra](foundation.composition-algebra.md)
- [Pullback-hom](orthogonal-factorization-systems.pullback-hom.md)
