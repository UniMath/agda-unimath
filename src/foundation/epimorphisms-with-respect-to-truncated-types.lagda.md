# Epimorphisms with respect to truncated types

```agda
module foundation.epimorphisms-with-respect-to-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.embeddings
open import foundation.functoriality-truncation
open import foundation.truncation-equivalences
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A map `f : A → B` is said to be a **`k`-epimorphism** if the precomposition
function

```text
  - ∘ f : (B → X) → (A → X)
```

is an embedding for every `k`-truncated type `X`.

## Definitions

### `k`-epimorphisms

```agda
is-epimorphism-Truncated-Type :
  {l1 l2 : Level} (l : Level) (k : 𝕋) {A : UU l1} {B : UU l2} →
  (A → B) → UU (l1 ⊔ l2 ⊔ lsuc l)
is-epimorphism-Truncated-Type l k f =
  (X : Truncated-Type l k) → is-emb (precomp f (type-Truncated-Type X))
```

## Properties

### Every `k+1`-epimorphism is a `k`-epimorphism

```agda
is-epimorphism-is-epimorphism-succ-Truncated-Type :
  {l1 l2 : Level} (l : Level) (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-epimorphism-Truncated-Type l (succ-𝕋 k) f →
  is-epimorphism-Truncated-Type l k f
is-epimorphism-is-epimorphism-succ-Truncated-Type l k f H X =
  H (truncated-type-succ-Truncated-Type k X)
```

### Every map is a `-1`-epimorphism

```agda
is-neg-one-epimorphism :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-epimorphism-Truncated-Type l3 neg-one-𝕋 f
is-neg-one-epimorphism f P =
  is-emb-is-prop
    ( is-prop-function-type (is-prop-type-Prop P))
    ( is-prop-function-type (is-prop-type-Prop P))
```

### Every `k`-equivalence is a `k`-epimorphism

```agda
is-epimorphism-is-truncation-equivalence-Truncated-Type :
  {l1 l2 : Level} (l : Level) (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-truncation-equivalence k f →
  is-epimorphism-Truncated-Type l k f
is-epimorphism-is-truncation-equivalence-Truncated-Type l k f H X =
  is-emb-is-equiv (is-equiv-precomp-is-truncation-equivalence k f H X)
```

### A map is a `k`-epimorphism if and only if its `k`-truncation is a `k`-epimorphism

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-epimorphism-is-epimorphism-map-trunc-Truncated-Type :
    is-epimorphism-Truncated-Type l3 k (map-trunc k f) →
    is-epimorphism-Truncated-Type l3 k f
  is-epimorphism-is-epimorphism-map-trunc-Truncated-Type H X =
    is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps
      ( precomp (map-trunc k f) (type-Truncated-Type X))
      ( precomp unit-trunc (type-Truncated-Type X))
      ( precomp unit-trunc (type-Truncated-Type X))
      ( precomp f (type-Truncated-Type X))
      ( precomp-coherence-square-maps
        ( unit-trunc)
        ( f)
        ( map-trunc k f)
        ( unit-trunc)
        ( inv-htpy (coherence-square-map-trunc k f))
        ( type-Truncated-Type X))
      ( is-truncation-trunc X)
      ( is-truncation-trunc X)
      ( H X)
```
