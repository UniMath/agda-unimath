# Limits of sequences in premetric spaces

```agda
module metric-spaces.limits-of-sequences-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subsequences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
open import metric-spaces.sequences-premetric-spaces
open import metric-spaces.short-functions-premetric-spaces
```

</details>

## Ideas

An element `v` of a [premetric space](metric-spaces.premetric-spaces.md) `M` is
the
{{#concept "limit" Disambiguation="of a sequence in a premetric space" Agda=is-limit-sequence-Premetric-Space}}
of a [sequence](metric-spaces.sequences-premetric-spaces.md) `u` in a
[premetric space](metric-spaces.premetric-spaces.md) `M` if there exists a
function `m : ℚ⁺ → ℕ` such that whenever `m ε ≤ n` in `ℕ`, `u n` is in an
[`ε`-neighborhood](metric-spaces.premetric-structures.md) of `l`. The function
`m` is called a
{{#concept "limit modulus" Disambiguation="of a sequence in a premetric space" Agda=limit-modulus-sequence-Premetric-Space}}
of the sequence `u` at `l`.
[Short maps](metric-spaces.short-functions-premetric-spaces.md) between
premetric spaces preserves limits.

## Definition

### Limits of sequences in a premetric space

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  (u : sequence-type-Premetric-Space M)
  (lim : type-Premetric-Space M)
  where

  is-limit-modulus-prop-sequence-Premetric-Space : (ℚ⁺ → ℕ) → Prop l2
  is-limit-modulus-prop-sequence-Premetric-Space m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℕ)
          ( λ (n : ℕ) →
            hom-Prop
              ( leq-ℕ-Prop (m ε) n)
              ( structure-Premetric-Space M ε (u n) lim)))

  is-limit-modulus-sequence-Premetric-Space : (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-sequence-Premetric-Space m =
    type-Prop (is-limit-modulus-prop-sequence-Premetric-Space m)

  limit-modulus-sequence-Premetric-Space : UU l2
  limit-modulus-sequence-Premetric-Space =
    type-subtype is-limit-modulus-prop-sequence-Premetric-Space

  modulus-limit-modulus-sequence-Premetric-Space :
    limit-modulus-sequence-Premetric-Space → ℚ⁺ → ℕ
  modulus-limit-modulus-sequence-Premetric-Space m = pr1 m

  is-modulus-limit-modulus-sequence-Premetric-Space :
    (m : limit-modulus-sequence-Premetric-Space) →
    is-limit-modulus-sequence-Premetric-Space
      (modulus-limit-modulus-sequence-Premetric-Space m)
  is-modulus-limit-modulus-sequence-Premetric-Space m = pr2 m

  is-limit-prop-sequence-Premetric-Space : Prop l2
  is-limit-prop-sequence-Premetric-Space =
    is-inhabited-subtype-Prop is-limit-modulus-prop-sequence-Premetric-Space

  is-limit-sequence-Premetric-Space : UU l2
  is-limit-sequence-Premetric-Space =
    type-Prop is-limit-prop-sequence-Premetric-Space
```

## Properties

### Short maps between premetric spaces preserve limits of sequences

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : short-function-Premetric-Space A B)
  (u : sequence-type-Premetric-Space A)
  (lim : type-Premetric-Space A)
  where

  short-map-limit-modulus-sequence-Premetric-Space :
    limit-modulus-sequence-Premetric-Space A u lim →
    limit-modulus-sequence-Premetric-Space B
      ( map-sequence
        ( map-short-function-Premetric-Space A B f)
        ( u))
      ( map-short-function-Premetric-Space A B f lim)
  short-map-limit-modulus-sequence-Premetric-Space =
    tot
      ( λ m H ε n →
        is-short-map-short-function-Premetric-Space A B f ε (u n) lim ∘
        H ε n)

  short-map-limit-sequence-Premetric-Space :
    is-limit-sequence-Premetric-Space A u lim →
    is-limit-sequence-Premetric-Space B
      ( map-sequence
        ( map-short-function-Premetric-Space A B f)
        ( u))
      ( map-short-function-Premetric-Space A B f lim)
  short-map-limit-sequence-Premetric-Space =
    map-is-inhabited short-map-limit-modulus-sequence-Premetric-Space
```

### A sequence in a premetric space has a limit if all its subsequences have this limit

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  (u : sequence-type-Premetric-Space M)
  (lim : type-Premetric-Space M)
  where

  reflects-limit-subsequence-Premetric-Space :
    ( ( v : subsequence u) →
      is-limit-sequence-Premetric-Space M
        ( seq-subsequence u v)
        ( lim)) →
    is-limit-sequence-Premetric-Space M u lim
  reflects-limit-subsequence-Premetric-Space H = H (refl-subsequence u)
```
