# Limits of sequences in pseudometric spaces

```agda
module metric-spaces.limits-of-sequences-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.subsequences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.limits-of-sequences-premetric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.sequences-pseudometric-spaces
```

</details>

## Ideas

{{#concept "Limits" Disambiguation="of sequences in pseudometric spaces" Agda=is-limit-sequence-Pseudometric-Space}}
of
[sequences in pseudometric spaces](metric-spaces.sequences-pseudometric-spaces.md)
are [limits](metric-spaces.limits-of-sequences-premetric-spaces.md) in the
underlying [premetric space](metric-spaces.premetric-spaces.md): there exists a
function `m : ℚ⁺ → ℕ` such that whenever `m ε ≤ n` in `ℕ`, `u n` is in an
[`ε`-neighborhood](metric-spaces.premetric-structures.md) of `l`.

Limits of a sequence in a pseudometric space are indistinguishable. The value of
a constant sequence in a pseudometric space is its limit.

## Definition

### Limits of sequences in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-type-Pseudometric-Space M)
  (lim : type-Pseudometric-Space M)
  where

  is-limit-modulus-prop-sequence-Pseudometric-Space : (ℚ⁺ → ℕ) → Prop l2
  is-limit-modulus-prop-sequence-Pseudometric-Space =
    is-limit-modulus-prop-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( u)
      ( lim)

  is-limit-modulus-sequence-Pseudometric-Space : (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-sequence-Pseudometric-Space m =
    type-Prop (is-limit-modulus-prop-sequence-Pseudometric-Space m)

  limit-modulus-sequence-Pseudometric-Space : UU l2
  limit-modulus-sequence-Pseudometric-Space =
    type-subtype is-limit-modulus-prop-sequence-Pseudometric-Space

  modulus-limit-modulus-sequence-Pseudometric-Space :
    limit-modulus-sequence-Pseudometric-Space → ℚ⁺ → ℕ
  modulus-limit-modulus-sequence-Pseudometric-Space m = pr1 m

  is-modulus-limit-modulus-sequence-Pseudometric-Space :
    (m : limit-modulus-sequence-Pseudometric-Space) →
    is-limit-modulus-sequence-Pseudometric-Space
      (modulus-limit-modulus-sequence-Pseudometric-Space m)
  is-modulus-limit-modulus-sequence-Pseudometric-Space m = pr2 m

  is-limit-prop-sequence-Pseudometric-Space : Prop l2
  is-limit-prop-sequence-Pseudometric-Space =
    is-inhabited-subtype-Prop is-limit-modulus-prop-sequence-Pseudometric-Space

  is-limit-sequence-Pseudometric-Space : UU l2
  is-limit-sequence-Pseudometric-Space =
    type-Prop is-limit-prop-sequence-Pseudometric-Space
```

## Properties

### The value of a constant sequence in a pseudometric space is its limit

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2) (x : type-Pseudometric-Space M)
  where

  limit-modulus-constant-sequence-Pseudometric-Space :
    limit-modulus-sequence-Pseudometric-Space M (const ℕ x) x
  limit-modulus-constant-sequence-Pseudometric-Space =
    ( λ _ → zero-ℕ) ,
    ( λ ε _ _ → is-reflexive-structure-Pseudometric-Space M ε x)

  limit-constant-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M (const ℕ x) x
  limit-constant-sequence-Pseudometric-Space =
    unit-trunc-Prop limit-modulus-constant-sequence-Pseudometric-Space
```

### Two limits of a sequence in a pseudometric space are indistinguishable

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-type-Pseudometric-Space M)
  (x y : type-Pseudometric-Space M)
  where

  indistinguishable-limit-limit-modulus-sequence-Pseudometric-Space :
    limit-modulus-sequence-Pseudometric-Space M u x →
    limit-modulus-sequence-Pseudometric-Space M u y →
    is-indistinguishable-Pseudometric-Space M x y
  indistinguishable-limit-limit-modulus-sequence-Pseudometric-Space mx my ε =
    tr
      ( is-upper-bound-dist-Pseudometric-Space M x y)
      ( eq-add-split-ℚ⁺ ε)
      ( tr-modulus-indistinguishable
        ( left-summand-split-ℚ⁺ ε)
        ( right-summand-split-ℚ⁺ ε)
        ( ( modulus-limit-modulus-sequence-Pseudometric-Space
            ( M)
            ( u)
            ( x)
            ( mx)
            ( left-summand-split-ℚ⁺ ε)) ,
          ( is-modulus-limit-modulus-sequence-Pseudometric-Space
            ( M)
            ( u)
            ( x)
            ( mx)
            ( left-summand-split-ℚ⁺ ε)))
        ( ( modulus-limit-modulus-sequence-Pseudometric-Space
            ( M)
            ( u)
            ( y)
            ( my)
            ( right-summand-split-ℚ⁺ ε)) ,
          ( is-modulus-limit-modulus-sequence-Pseudometric-Space
            ( M)
            ( u)
            ( y)
            ( my)
            ( right-summand-split-ℚ⁺ ε))))
    where
      tr-modulus-indistinguishable :
        (d₁ d₂ : ℚ⁺) →
        Σ ( ℕ)
          ( λ N →
            (n : ℕ) →
            leq-ℕ N n →
            neighborhood-Pseudometric-Space M d₁ (u n) x) →
        Σ ( ℕ)
          ( λ N →
            (n : ℕ) →
            leq-ℕ N n →
            neighborhood-Pseudometric-Space M d₂ (u n) y) →
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

  indistinguishable-limit-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M u x →
    is-limit-sequence-Pseudometric-Space M u y →
    is-indistinguishable-Pseudometric-Space M x y
  indistinguishable-limit-sequence-Pseudometric-Space Lx Ly =
    rec-trunc-Prop
      ( is-indistinguishable-prop-Pseudometric-Space M x y)
      ( λ My →
        rec-trunc-Prop
          ( Π-Prop ℚ⁺ (λ d → structure-Pseudometric-Space M d x y))
          ( λ Mx →
            indistinguishable-limit-limit-modulus-sequence-Pseudometric-Space
              Mx
              My)
          ( Lx))
      ( Ly)
```

### Taking subsequences preserves limits in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-type-Pseudometric-Space M)
  (v : subsequence u)
  (lim : type-Pseudometric-Space M)
  where

  modulus-subsequence-limit-modulus-sequence-Premetric-Space :
    limit-modulus-sequence-Pseudometric-Space M u lim →
    limit-modulus-sequence-Pseudometric-Space
      ( M)
      ( seq-subsequence u v)
      ( lim)
  modulus-subsequence-limit-modulus-sequence-Premetric-Space =
    tot
      ( λ m is-modulus d n H →
        is-modulus
          ( d)
          ( extract-subsequence u v n)
          ( transitive-leq-ℕ
            ( m d)
            ( n)
            ( extract-subsequence u v n)
            ( is-superlinear-extract-subsequence u v n)
            ( H)))

  preserves-limit-subsequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M u lim →
    is-limit-sequence-Pseudometric-Space M (seq-subsequence u v) lim
  preserves-limit-subsequence-Pseudometric-Space =
    map-is-inhabited modulus-subsequence-limit-modulus-sequence-Premetric-Space
```
