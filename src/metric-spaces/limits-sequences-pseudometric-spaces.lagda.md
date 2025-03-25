# Limits of sequences in pseudometric spaces

```agda
module metric-spaces.limits-sequences-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.monotonic-sequences-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.eventually-constant-sequences
open import foundation.eventually-equal-sequences
open import foundation.functoriality-dependent-pair-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subsequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.limits-sequences-premetric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.sequences-pseudometric-spaces
```

</details>

## Ideas

{{#concept "Limits" Disambiguation="of sequences in pseudometric spaces" Agda=is-limit-sequence-Pseudometric-Space}}
of
[sequences in pseudometric spaces](metric-spaces.sequences-pseudometric-spaces.md)
are [limits](metric-spaces.limits-sequences-premetric-spaces.md) in the
underlying [premetric space](metric-spaces.premetric-spaces.md).

Limits of a sequence in a pseudometric space are indistinguishable. The value of
a constant sequence in a pseudometric space is its limit; the eventual values of
an [eventually constant](foundation.eventually-constant-sequences.md) sequence
in a pseudometric are limits of the sequence.

Asymptotic indistinguishability of sequences in pseudometric spaces preserves
limits.

## Definition

### Limits of sequences in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (l : type-Pseudometric-Space M)
  where

  is-modulus-limit-sequence-Pseudometric-Space :
    (d : ℚ⁺) (N : ℕ) → UU l2
  is-modulus-limit-sequence-Pseudometric-Space =
    is-modulus-limit-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( u)
      ( l)

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

### Eventual values of eventually constant sequences in pseudometric spaces are limits

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (H : is-eventually-constant-sequence u)
  where

  limit-value-asymtpotically-constant-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M u
      (value-eventually-constant-sequence u H)
  limit-value-asymtpotically-constant-sequence-Pseudometric-Space =
    preserves-limit-eventually-eq-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( const ℕ (value-eventually-constant-sequence u H))
      ( u)
      ( eventually-eq-constant-sequence u H)
      ( value-eventually-constant-sequence u H)
      ( limit-constant-sequence-Pseudometric-Space M
        ( value-eventually-constant-sequence u H))
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
  indistinguishable-limit-sequence-Pseudometric-Space =
    Π-merge-family-ℚ⁺
      ( is-upper-bound-dist-Pseudometric-Space M x y)
      ( tr-modulus-indistinguishable)
    where
      tr-modulus-indistinguishable :
        (d₁ d₂ : ℚ⁺) →
        Σ ℕ (is-modulus-limit-sequence-Pseudometric-Space M u x d₁) →
        Σ ℕ (is-modulus-limit-sequence-Pseudometric-Space M u y d₂) →
        neighborhood-Pseudometric-Space M (d₁ +ℚ⁺ d₂) x y
      tr-modulus-indistinguishable d₁ d₂ (Nx , Mx) (Ny , My) =
        ( is-triangular-structure-Pseudometric-Space M
          ( x)
          ( u (max-ℕ Nx Ny))
          ( y)
          ( d₁)
          ( d₂)
          ( My (max-ℕ Nx Ny) (right-leq-max-ℕ Nx Ny))
          ( is-symmetric-structure-Pseudometric-Space M d₁
            ( u (max-ℕ Nx Ny))
            ( x)
            ( Mx (max-ℕ Nx Ny) (left-leq-max-ℕ Nx Ny))))
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
      ( modulus-is-unbounded-is-strictly-increasing-sequence-ℕ
        ( extract-subsequence u v)
        ( is-strictly-increasing-extract-subsequence u v))
      ( λ N is-modulus-N p I →
        is-modulus-N
          ( extract-subsequence u v p)
          ( leq-bound-is-strictly-increasing-sequence-ℕ
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( N)
            ( p)
            ( I)))
      ( L d)
```

### Asymptotical indistinguishability of sequences in a pseudometric space preserves limits

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u v : sequence-Pseudometric-Space M)
  (K : is-asymptotically-indistinguishable-sequence-Pseudometric-Space M u v)
  (l : type-Pseudometric-Space M)
  (L : is-limit-sequence-Pseudometric-Space M u l)
  where

  preserves-limit-asymptotically-indistinguishable-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M v l
  preserves-limit-asymptotically-indistinguishable-sequence-Pseudometric-Space =
    transitive-asymptotically-indistinguishable-sequence-Pseudometric-Space
      ( M)
      ( v)
      ( u)
      ( const ℕ l)
      ( L)
      ( symmetric-asymptotically-indistinguishable-sequence-Pseudometric-Space
        ( M)
        ( u)
        ( v)
        ( K))
```
