# The field of real numbers

```agda
module real-numbers.field-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields
open import commutative-algebra.invertible-elements-commutative-rings
open import commutative-algebra.trivial-commutative-rings

open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.universe-levels

open import real-numbers.apartness-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.local-ring-of-real-numbers
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The [real numbers](real-numbers.dedekind-real-numbers.md) form a
[Heyting field](commutative-algebra.heyting-fields.md) at each
[universe level](foundation.universe-levels.md).

## Definition

```agda
abstract
  is-nontrivial-commutative-ring-ℝ :
    (l : Level) → is-nontrivial-Commutative-Ring (commutative-ring-ℝ l)
  is-nontrivial-commutative-ring-ℝ l 0=1ℝ =
    neq-zero-one-ℚ
      ( is-injective-real-ℚ
        ( eq-sim-ℝ
          ( similarity-reasoning-ℝ
              zero-ℝ
              ~ℝ raise-ℝ l zero-ℝ
                by sim-raise-ℝ l zero-ℝ
              ~ℝ raise-ℝ l one-ℝ
                by sim-eq-ℝ 0=1ℝ
              ~ℝ one-ℝ
                by sim-raise-ℝ' l one-ℝ)))

  is-zero-is-noninvertible-commutative-ring-ℝ :
    (l : Level) (x : ℝ l) →
    ¬ is-invertible-element-Commutative-Ring (commutative-ring-ℝ l) x →
    x ＝ raise-ℝ l zero-ℝ
  is-zero-is-noninvertible-commutative-ring-ℝ l x ¬inv-x =
    eq-sim-ℝ
      ( sim-nonapart-ℝ _ _
        ( λ x#raise-l-zero →
          ¬inv-x
            ( is-invertible-is-nonzero-ℝ
              ( x)
              ( apart-right-sim-ℝ
                ( x)
                ( raise-ℝ l zero-ℝ)
                ( zero-ℝ)
                ( sim-raise-ℝ' l zero-ℝ)
                ( x#raise-l-zero)))))

  is-heyting-field-local-commutative-ring-ℝ :
    (l : Level) →
    is-heyting-field-Local-Commutative-Ring (local-commutative-ring-ℝ l)
  is-heyting-field-local-commutative-ring-ℝ l =
    ( is-nontrivial-commutative-ring-ℝ l ,
      is-zero-is-noninvertible-commutative-ring-ℝ l)

heyting-field-ℝ : (l : Level) → Heyting-Field (lsuc l)
heyting-field-ℝ l =
  ( local-commutative-ring-ℝ l ,
    is-heyting-field-local-commutative-ring-ℝ l)
```
