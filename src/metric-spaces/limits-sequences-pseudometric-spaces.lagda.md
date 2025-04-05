# Limits of sequences in pseudometric spaces

```agda
module metric-spaces.limits-sequences-pseudometric-spaces where
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
open import foundation.subtypes
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
a constant sequence in a pseudometric space is its limit.

## Definition

### Limits of sequences in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (l : type-Pseudometric-Space M)
  where

  is-modulus-limit-prop-sequence-Pseudometric-Space : (ℚ⁺ → ℕ) → Prop l2
  is-modulus-limit-prop-sequence-Pseudometric-Space =
    is-modulus-limit-prop-sequence-Premetric-Space
      ( premetric-Pseudometric-Space M)
      ( u)
      ( l)

  is-modulus-limit-sequence-Pseudometric-Space : (ℚ⁺ → ℕ) → UU l2
  is-modulus-limit-sequence-Pseudometric-Space m =
    type-Prop (is-modulus-limit-prop-sequence-Pseudometric-Space m)

  modulus-limit-sequence-Pseudometric-Space : UU l2
  modulus-limit-sequence-Pseudometric-Space =
    type-subtype is-modulus-limit-prop-sequence-Pseudometric-Space

  modulus-modulus-limit-sequence-Pseudometric-Space :
    modulus-limit-sequence-Pseudometric-Space → ℚ⁺ → ℕ
  modulus-modulus-limit-sequence-Pseudometric-Space m = pr1 m

  is-modulus-modulus-limit-sequence-Pseudometric-Space :
    (m : modulus-limit-sequence-Pseudometric-Space) →
    is-modulus-limit-sequence-Pseudometric-Space
      (modulus-modulus-limit-sequence-Pseudometric-Space m)
  is-modulus-modulus-limit-sequence-Pseudometric-Space m = pr2 m

  is-limit-prop-sequence-Pseudometric-Space : Prop l2
  is-limit-prop-sequence-Pseudometric-Space =
    is-inhabited-subtype-Prop is-modulus-limit-prop-sequence-Pseudometric-Space

  is-limit-sequence-Pseudometric-Space : UU l2
  is-limit-sequence-Pseudometric-Space =
    type-Prop is-limit-prop-sequence-Pseudometric-Space
```

## Properties

### Constant sequences in pseudometric spaces have limit equal to their value

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2) (x : type-Pseudometric-Space M)
  where

  modulus-limit-constant-sequence-Pseudometric-Space :
    modulus-limit-sequence-Pseudometric-Space M (const ℕ x) x
  modulus-limit-constant-sequence-Pseudometric-Space =
    ( λ _ → zero-ℕ) ,
    ( λ ε _ _ → is-reflexive-structure-Pseudometric-Space M ε x)

  limit-constant-sequence-Pseudometric-Space :
    is-limit-sequence-Pseudometric-Space M (const ℕ x) x
  limit-constant-sequence-Pseudometric-Space =
    unit-trunc-Prop modulus-limit-constant-sequence-Pseudometric-Space
```

### Two limits of a sequence in a pseudometric space are indistinguishable

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : sequence-Pseudometric-Space M)
  (x y : type-Pseudometric-Space M)
  where

  indistinguishable-limit-modulus-limit-sequence-Pseudometric-Space :
    modulus-limit-sequence-Pseudometric-Space M u x →
    modulus-limit-sequence-Pseudometric-Space M u y →
    is-indistinguishable-Pseudometric-Space M x y
  indistinguishable-limit-modulus-limit-sequence-Pseudometric-Space mx my =
    Π-merge-family-ℚ⁺
      ( λ d →
        Σ ( ℕ)
          ( λ N →
            (n : ℕ) →
            leq-ℕ N n →
            neighborhood-Pseudometric-Space M d (u n) x))
      ( λ d →
        Σ ( ℕ)
          ( λ N →
            (n : ℕ) →
            leq-ℕ N n →
            neighborhood-Pseudometric-Space M d (u n) y))
      ( is-upper-bound-dist-Pseudometric-Space M x y)
      ( tr-modulus-indistinguishable)
      ( λ d →
        modulus-modulus-limit-sequence-Pseudometric-Space M u x mx d ,
        is-modulus-modulus-limit-sequence-Pseudometric-Space M u x mx d)
      ( λ d →
        modulus-modulus-limit-sequence-Pseudometric-Space M u y my d ,
        is-modulus-modulus-limit-sequence-Pseudometric-Space M u y my d)
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
            indistinguishable-limit-modulus-limit-sequence-Pseudometric-Space
              Mx
              My)
          ( Lx))
      ( Ly)
```

### Subsequences preserve limits in pseudometric spaces

```agda
-- module _
--   {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
--   (u : sequence-Pseudometric-Space M)
--   (l : type-Pseudometric-Space M)
--   (L : is-limit-sequence-Pseudometric-Space M u l)
--   (v : subsequence u)
--   where

--   preserves-limit-subsequence-Pseudometric-Space :
--     is-limit-sequence-Pseudometric-Space M (sequence-subsequence u v) l
--   preserves-limit-subsequence-Pseudometric-Space d =
--     map-Σ
--       ( is-modulus-limit-sequence-Premetric-Space
--         ( premetric-Pseudometric-Space M)
--         ( sequence-subsequence u v)
--         ( l)
--         ( d))
--       ( modulus-is-unbounded-is-strictly-increasing-sequence-ℕ
--         ( extract-subsequence u v)
--         ( is-strictly-increasing-extract-subsequence u v))
--       ( λ N is-modulus-N p I →
--         is-modulus-N
--           ( extract-subsequence u v p)
--           ( leq-bound-is-strictly-increasing-sequence-ℕ
--             ( extract-subsequence u v)
--             ( is-strictly-increasing-extract-subsequence u v)
--             ( N)
--             ( p)
--             ( I)))
--       ( L d)
```
