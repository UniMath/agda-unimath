# Epimorphisms with respect to truncated types

```agda
module foundation.epimorphisms-with-respect-to-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-function-types
open import foundation.propositions
open import foundation.truncated-types
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

A map `f : A → B` is said to be a **`k`-epimorphism** if the precomposition function

```md
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
