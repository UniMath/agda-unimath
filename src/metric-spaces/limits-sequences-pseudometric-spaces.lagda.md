# Limits of sequences in pseudometric spaces

```agda
module metric-spaces.limits-sequences-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.monotonic-endomaps-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.asymptotically-constant-sequences
open import foundation.asymptotically-equal-sequences
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subsequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.limits-sequences-premetric-spaces
open import metric-spaces.premetric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.sequences-pseudometric-spaces
open import metric-spaces.short-functions-premetric-spaces
```

</details>

## Ideas

{{#concept "Limits" Disambiguation="of sequences in pseudometric spaces" Agda=is-limit-sequence-Pseudometric-Space}}
of sequences in pseudometric spaces are
[limits](metric-spaces.limits-sequences-premetric-spaces.md) in the underlying
[premetric space](metric-spaces.premetric-spaces.md).

## Definition

### Limits of sequences in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (l : type-Pseudometric-Space M)
  where

  is-limit-sequence-Pseudometric-Space : UU l2
  is-limit-sequence-Pseudometric-Space =
    is-limit-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( u)
      ( l)

  modulus-limit-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space → ℚ⁺ → ℕ
  modulus-limit-sequence-Pseudometric-Space =
    modulus-limit-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( u)
      ( l)

  is-modulus-modulus-limit-sequence-Pseudometric-Space :
    (H : is-limit-sequence-Pseudometric-Space) (d : ℚ⁺) →
    (n : ℕ) (I : leq-ℕ (modulus-limit-sequence-Pseudometric-Space H d) n) →
    neighborhood-Pseudometric-Space M d (u n) l
  is-modulus-modulus-limit-sequence-Pseudometric-Space =
    is-modulus-modulus-limit-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( u)
      ( l)
```

## Properties

### Constant sequences in pseudometric spaces have limit equal to their value

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2) (x : type-Pseudometric-Space M)
  where

  limit-constant-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M (const ℕ x) x
  limit-constant-sequence-Pseudometric-Space d =
    zero-ℕ , λ _ _ → is-reflexive-structure-Pseudometric-Space M d x
```

### Asymptotical values of asymptotically constant sequences in pseudometric spaces are limits

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (H : is-asymptotically-constant-sequence u)
  where

  limit-value-asymtpotically-constant-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M u
      (value-asymptotically-constant-sequence u H)
  limit-value-asymtpotically-constant-sequence-Pseudometric-Space =
    preserves-limit-asymptotically-eq-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( const ℕ (value-asymptotically-constant-sequence u H))
      ( u)
      ( asymptotically-eq-constant-sequence u H)
      ( value-asymptotically-constant-sequence u H)
      ( limit-constant-sequence-Pseudometric-Space M
        ( value-asymptotically-constant-sequence u H))
```

### Two limits of a sequence in a pseudometric space are indistinguishable

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (x y : type-Pseudometric-Space M)
  where

  indistinguishable-limit-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M u x →
    is-limit-sequence-Pseudometric-Space M u y →
    is-indistinguishable-Pseudometric-Space M x y
  indistinguishable-limit-sequence-Pseudometric-Space Lx Ly d =
    tr
      ( is-upper-bound-dist-Pseudometric-Space M x y)
      ( eq-add-split-ℚ⁺ d)
      ( is-triangular-structure-Pseudometric-Space M
        ( x)
        ( u N)
        ( y)
        ( d₁)
        ( d₂)
        ( is-modulus-modulus-limit-sequence-Pseudometric-Space M u y Ly d₂ N
          (right-leq-max-ℕ Nx Ny))
        ( is-symmetric-structure-Pseudometric-Space M d₁ (u N) x
          ( is-modulus-modulus-limit-sequence-Pseudometric-Space M u x Lx d₁ N
            (left-leq-max-ℕ Nx Ny))))
    where
      d₁ : ℚ⁺
      d₁ = left-summand-split-ℚ⁺ d

      d₂ : ℚ⁺
      d₂ = right-summand-split-ℚ⁺ d

      Nx : ℕ
      Nx = modulus-limit-sequence-Pseudometric-Space M u x Lx d₁

      Ny : ℕ
      Ny = modulus-limit-sequence-Pseudometric-Space M u y Ly d₂

      N : ℕ
      N = max-ℕ Nx Ny
```

### Subsequences preserve limits in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (l : type-Pseudometric-Space M)
  (L : is-limit-sequence-Pseudometric-Space M u l)
  (v : subsequence u)
  where

  preserves-limit-subsequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M (sequence-subsequence u v) l
  preserves-limit-subsequence-Pseudometric-Space d =
    map-Σ
      ( is-modulus-limit-sequence-Premetric-Space
        ( premetric-Pseudometric-Space M)
        ( sequence-subsequence u v)
        ( l)
        ( d))
      ( modulus-is-unbounded-is-strictly-increasing-endomap-ℕ
        ( extract-subsequence u v)
        ( is-strictly-increasing-extract-subsequence u v))
      ( λ N is-modulus-N p I →
        is-modulus-N
          ( extract-subsequence u v p)
          ( leq-bound-is-strictly-increasing-endomap-ℕ
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( N)
            ( p)
            ( I)))
      ( L d)
```
