# Limits of sequences in premetric spaces

```agda
module metric-spaces.limits-sequences-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.asymptotically-equal-sequences
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subsequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
open import metric-spaces.sequences-premetric-spaces
open import metric-spaces.short-functions-premetric-spaces
```

</details>

## Ideas

An element `l : type-Premetric-Space M` is the
{{#concept "limit" Disambiguation="of a sequence in a premetric space" Agda=is-limit-sequence-Premetric-Space}}
of a [sequence](metric-spaces.sequences-premetric-spaces.md) `u` in a
[premetric space](metric-spaces.premetric-spaces.md) `M` if
[`d`-neighborhoods](metric-spaces.premetric-structures.md) of `l` contain all
the terms `u n` for sufficiently large `n : ℕ`; i.e. if `u` is asymptotically
indistinguishable from the constant sequence `l`.

[Short maps](metric-spaces.short-functions-premetric-spaces.md) between
premetric spaces and
[asymptotical equality](foundation.asymptotically-equal-sequences.md) of
sequences preserve limits.

## Definition

### Limits of sequences in premetric spaces

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  (u : sequence-Premetric-Space M)
  (l : type-Premetric-Space M)
  where

  is-modulus-limit-prop-sequence-Premetric-Space : (d : ℚ⁺) (N : ℕ) → Prop l2
  is-modulus-limit-prop-sequence-Premetric-Space d N =
    Π-Prop
      ( ℕ)
      ( λ (n : ℕ) →
        hom-Prop (leq-ℕ-Prop N n) (structure-Premetric-Space M d (u n) l))

  is-modulus-limit-sequence-Premetric-Space : (d : ℚ⁺) (N : ℕ) → UU l2
  is-modulus-limit-sequence-Premetric-Space d N =
    type-Prop (is-modulus-limit-prop-sequence-Premetric-Space d N)

  is-limit-sequence-Premetric-Space : UU l2
  is-limit-sequence-Premetric-Space =
    (d : ℚ⁺) → Σ ℕ (is-modulus-limit-sequence-Premetric-Space d)

  eq-const-is-limit-sequence-Premetric-Space :
    is-limit-sequence-Premetric-Space ＝
    is-asymptotically-indistinguishable-sequence-Premetric-Space
      ( M)
      ( u)
      ( const ℕ l)
  eq-const-is-limit-sequence-Premetric-Space = refl

  modulus-limit-sequence-Premetric-Space :
    is-limit-sequence-Premetric-Space → ℚ⁺ → ℕ
  modulus-limit-sequence-Premetric-Space H d = pr1 (H d)

  is-modulus-modulus-limit-sequence-Premetric-Space :
    (H : is-limit-sequence-Premetric-Space) (d : ℚ⁺) →
    is-modulus-limit-sequence-Premetric-Space
      ( d)
      ( modulus-limit-sequence-Premetric-Space H d)
  is-modulus-modulus-limit-sequence-Premetric-Space H d = pr2 (H d)
```

## Properties

### Asymptotical equality of sequences preserves limits

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  (u v : sequence-Premetric-Space M)
  (E : asymptotically-eq-sequence u v)
  (l : type-Premetric-Space M)
  (L : is-limit-sequence-Premetric-Space M u l)
  where

  preserves-limit-asymptotically-eq-sequence-Premetric-Space :
    is-limit-sequence-Premetric-Space M v l
  pr1 (preserves-limit-asymptotically-eq-sequence-Premetric-Space d) =
    max-ℕ
      ( modulus-asymptotically-eq-sequence u v E)
      ( modulus-limit-sequence-Premetric-Space M u l L d)
  pr2 (preserves-limit-asymptotically-eq-sequence-Premetric-Space d) n I =
    tr
      ( λ x → neighborhood-Premetric-Space M d x l)
      ( eq-leq-modulus-asymptotically-eq-sequence u v E n
        ( leq-left-leq-max-ℕ n
          ( modulus-asymptotically-eq-sequence u v E)
          ( modulus-limit-sequence-Premetric-Space M u l L d)
          ( I)))
      ( is-modulus-modulus-limit-sequence-Premetric-Space M u l L d n
        ( leq-right-leq-max-ℕ n
          ( modulus-asymptotically-eq-sequence u v E)
          ( modulus-limit-sequence-Premetric-Space M u l L d)
          ( I)))
```

### Short maps between premetric spaces preserve limits of sequences

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : short-function-Premetric-Space A B)
  (u : sequence-Premetric-Space A)
  (l : type-Premetric-Space A)
  (L : is-limit-sequence-Premetric-Space A u l)
  where

  short-map-limit-sequence-Premetric-Space :
    is-limit-sequence-Premetric-Space
      ( B)
      ( map-sequence
        ( map-short-function-Premetric-Space A B f)
        ( u))
      ( map-short-function-Premetric-Space A B f l)
  short-map-limit-sequence-Premetric-Space d =
    tot tr-modulus (L d)
    where
      tr-modulus :
        (N : ℕ) →
        is-modulus-limit-sequence-Premetric-Space A u l d N →
        is-modulus-limit-sequence-Premetric-Space B
          ( map-sequence
            ( map-short-function-Premetric-Space A B f)
            ( u))
          ( map-short-function-Premetric-Space A B f l)
          ( d)
          ( N)
      tr-modulus N I p H =
        is-short-map-short-function-Premetric-Space A B f d
          ( u p)
          ( l)
          ( I p H)
```

### A sequence in a premetric space has a limit if all its subsequences have this limit

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  (u : sequence-Premetric-Space M)
  (x : type-Premetric-Space M)
  where

  reflects-limit-subsequence-Premetric-Space :
    ( ( v : subsequence u) →
      is-limit-sequence-Premetric-Space M
        ( sequence-subsequence u v)
        ( x)) →
    is-limit-sequence-Premetric-Space M u x
  reflects-limit-subsequence-Premetric-Space H = H (refl-subsequence u)
```
