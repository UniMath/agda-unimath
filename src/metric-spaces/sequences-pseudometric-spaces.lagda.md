# Sequences in pseudometric spaces

```agda
module metric-spaces.sequences-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces
```

</details>

## Ideas

A
{{#concept "sequence" Disambiguation="in a pseudometric space" Agda=sequence-Pseudometric-Space}}
in a [pseudometric space](metric-spaces.pseudometric-spaces.md) is a
[sequence in its underlying premetric space](metric-spaces.sequences-premetric-spaces.md).

Two sequences `u v : sequence-Pseudometric-Space M` are
{{#concept "asymptotically indistinguishable" Disambiguation="sequences in a pseudometric space" Agda=is-asymptotically-indistinguishable-sequence-Pseudometric-Space}}
if they are as sequences in the underlying premetric space.

Asymptotical indistinguishability of sequences in a pseudometric space is
reflexive, symmetric and transitive.

## Definition

### Sequences in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  sequence-Pseudometric-Space : UU l1
  sequence-Pseudometric-Space = sequence (type-Pseudometric-Space M)
```

### Asymptotically indistinguishable sequences in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u v : sequence-Pseudometric-Space M)
  where

  is-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space :
    (d : ℚ⁺) (N : ℕ) → UU l2
  is-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space d N =
    (n : ℕ) → leq-ℕ N n → neighborhood-Pseudometric-Space M d (u n) (v n)

  has-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space :
    (d : ℚ⁺) → UU l2
  has-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space d =
    Σ ( ℕ)
      ( is-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space
        ( d))

  is-asymptotically-indistinguishable-sequence-Pseudometric-Space : UU l2
  is-asymptotically-indistinguishable-sequence-Pseudometric-Space =
    (d : ℚ⁺) →
    has-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space d
```

## Properties

### Asymptotical indistinguishability of sequences in a pseudometric space is reflexive

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  where

  refl-asymptotically-indistinguishable-sequence-Pseudometric-Space :
    is-asymptotically-indistinguishable-sequence-Pseudometric-Space M u u
  refl-asymptotically-indistinguishable-sequence-Pseudometric-Space d =
    zero-ℕ , λ n _ → is-reflexive-structure-Pseudometric-Space M d (u n)
```

### Asymptotical indistinguishability of sequences in a pseudometric space is symmetric

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u v : sequence-Pseudometric-Space M)
  where

  symmetric-asymptotically-indistinguishable-sequence-Pseudometric-Space :
    is-asymptotically-indistinguishable-sequence-Pseudometric-Space M u v →
    is-asymptotically-indistinguishable-sequence-Pseudometric-Space M v u
  symmetric-asymptotically-indistinguishable-sequence-Pseudometric-Space I d =
    tot
      ( λ N H p K →
        is-symmetric-structure-Pseudometric-Space M d (u p) (v p) (H p K))
      ( I d)
```

### Asymptotical indistinguishability of sequences in a pseudometric space is transitive

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u v w : sequence-Pseudometric-Space M)
  where

  transitive-asymptotically-indistinguishable-sequence-Pseudometric-Space :
    is-asymptotically-indistinguishable-sequence-Pseudometric-Space M v w →
    is-asymptotically-indistinguishable-sequence-Pseudometric-Space M u v →
    is-asymptotically-indistinguishable-sequence-Pseudometric-Space M u w
  transitive-asymptotically-indistinguishable-sequence-Pseudometric-Space I J =
    Π-split-family-ℚ⁺
      ( has-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space
        ( M)
        ( u)
        ( w))
      ( tr-modulus-indistinguishable)
      ( J)
      ( I)
    where
    tr-modulus-indistinguishable :
      (d₁ d₂ : ℚ⁺) →
      has-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space
        ( M)
        ( u)
        ( v)
        ( d₁) →
      has-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space
        ( M)
        ( v)
        ( w)
        ( d₂) →
      has-modulus-asymptotically-indistinguishable-sequence-Pseudometric-Space
        ( M)
        ( u)
        ( w)
        ( d₁ +ℚ⁺ d₂)
    tr-modulus-indistinguishable d₁ d₂ (n , Hn) (m , Hm) =
      max-ℕ m n ,
      λ p max≤p →
      is-triangular-structure-Pseudometric-Space
        ( M)
        ( u p)
        ( v p)
        ( w p)
        ( d₁)
        ( d₂)
        ( Hm p (leq-left-leq-max-ℕ p m n max≤p))
        ( Hn p (leq-right-leq-max-ℕ p m n max≤p))
```
