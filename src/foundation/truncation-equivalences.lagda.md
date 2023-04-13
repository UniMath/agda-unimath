# `k`-equivalences

```agda
module foundation.truncation-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-function-types
open import foundation.functoriality-truncation
open import foundation.homotopies
open import foundation.truncated-types
open import foundation.truncations
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

A map `f : A → B` is said to be a `k`-equivalence if the map `map-trunc k f : trunc k A → trunc k B` is an equivalence.

## Definition

```agda
is-truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-truncation-equivalence k f = is-equiv (map-trunc k f)

truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
truncation-equivalence k A B = Σ (A → B) (is-truncation-equivalence k)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  (f : truncation-equivalence k A B)
  where

  map-truncation-equivalence : A → B
  map-truncation-equivalence = pr1 f

  is-truncation-equivalence-truncation-equivalence :
    is-truncation-equivalence k map-truncation-equivalence
  is-truncation-equivalence-truncation-equivalence = pr2 f
```

## Properties

### A map `f : A → B` is a `k`-equivalence if and only if `- ∘ f : (B → X) → (A → X)` is an equivalence for every `k`-truncated type `X`

```agda
is-equiv-precomp-is-truncation-equivalence :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-truncation-equivalence k f →
  (X : Truncated-Type l3 k) → is-equiv (precomp f (type-Truncated-Type X))
is-equiv-precomp-is-truncation-equivalence k f H X =
  is-equiv-bottom-is-equiv-top-square
    ( precomp unit-trunc (type-Truncated-Type X))
    ( precomp unit-trunc (type-Truncated-Type X))
    ( precomp (map-trunc k f) (type-Truncated-Type X))
    ( precomp f (type-Truncated-Type X))
    ( htpy-precomp
      ( inv-htpy (coherence-square-map-trunc k f))
      ( type-Truncated-Type X))
    ( is-truncation-trunc X)
    ( is-truncation-trunc X)
    ( is-equiv-precomp-is-equiv (map-trunc k f) H (type-Truncated-Type X))

is-truncation-equivalence-is-equiv-precomp :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  ( (l : Level) (X : Truncated-Type l k) →
    is-equiv (precomp f (type-Truncated-Type X))) →
  is-truncation-equivalence k f
is-truncation-equivalence-is-equiv-precomp k {A} {B} f H =
  is-equiv-is-equiv-precomp-Truncated-Type k
    ( trunc k A)
    ( trunc k B)
    ( map-trunc k f)
    ( λ X →
      is-equiv-top-is-equiv-bottom-square
        ( precomp unit-trunc (type-Truncated-Type X))
        ( precomp unit-trunc (type-Truncated-Type X))
        ( precomp (map-trunc k f) (type-Truncated-Type X))
        ( precomp f (type-Truncated-Type X))
        ( htpy-precomp
          ( inv-htpy (coherence-square-map-trunc k f))
          ( type-Truncated-Type X))
        ( is-truncation-trunc X)
        ( is-truncation-trunc X)
        ( H _ X))
```
