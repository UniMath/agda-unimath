# Sequences in premetric spaces

```agda
module metric-spaces.sequences-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
open import metric-spaces.short-functions-premetric-spaces
```

</details>

## Ideas

A
{{#concept "sequence" Disambiguation="in a premetric space" Agda=sequence-Premetric-Space}}
in a [premetric space](metric-spaces.premetric-spaces.md) is a sequence in its
underlying type.

Two sequences `u v : sequence-Premetric-Space M` are
{{#concept "asymptotically indistinguishable" Disambiguation="sequences in a premetric space" Agda=is-asymptotically-indistinguishable-sequence-Premetric-Space}}
if, for any `d : ℚ⁺`, `u n` and `v n` are
[`d`-neighbors](metric-spaces.premetric-structures.md) for sufficiently large
`n : ℕ`.

## Definitions

### Sequences in premetric spaces

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  where

  sequence-Premetric-Space : UU l1
  sequence-Premetric-Space = sequence (type-Premetric-Space M)
```

### Asymptotically indistinguishable sequences in a premetric space

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  (u v : sequence-Premetric-Space M)
  where

  is-modulus-asymptotically-indistinguishable-sequence-Premetric-Space :
    (d : ℚ⁺) (N : ℕ) → UU l2
  is-modulus-asymptotically-indistinguishable-sequence-Premetric-Space d N =
    (n : ℕ) → leq-ℕ N n → neighborhood-Premetric-Space M d (u n) (v n)

  is-asymptotically-indistinguishable-sequence-Premetric-Space : UU l2
  is-asymptotically-indistinguishable-sequence-Premetric-Space =
    (d : ℚ⁺) →
    Σ ℕ (is-modulus-asymptotically-indistinguishable-sequence-Premetric-Space d)
```

## Properties

### Short maps between premetric spaces preserve asymptotical indistinguishability

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2)
  (B : Premetric-Space l1' l2')
  (f : short-function-Premetric-Space A B)
  (u v : sequence-Premetric-Space A)
  (H : is-asymptotically-indistinguishable-sequence-Premetric-Space A u v)
  where

  short-map-asymptotically-indistinguishable-sequence-Premetric-Space :
    is-asymptotically-indistinguishable-sequence-Premetric-Space B
      (map-sequence (map-short-function-Premetric-Space A B f) u)
      (map-sequence (map-short-function-Premetric-Space A B f) v)
  short-map-asymptotically-indistinguishable-sequence-Premetric-Space d =
    tot
      ( λ n K p I →
        is-short-map-short-function-Premetric-Space A B f
          ( d)
          ( u p)
          ( v p)
          ( K p I))
      ( H d)
```
