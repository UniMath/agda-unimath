# Equality of rational numbers

```agda
module elementary-number-theory.equality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

[Equality](foundation-core.identity-types.md) of
[rational numbers](elementary-number-theory.rational-numbers.md) is
characterized by similarity of the underlying
[integer fractions](elementary-number-theory.integer-fractions.md): `a/b` is
equal to `c/d` if and only if `a * d ＝ c * b`.

## Definitions

```agda
Eq-ℚ : ℚ → ℚ → UU lzero
Eq-ℚ x y = sim-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

refl-Eq-ℚ : (x : ℚ) → Eq-ℚ x x
refl-Eq-ℚ q = refl-sim-fraction-ℤ (fraction-ℚ q)

Eq-eq-ℚ : {x y : ℚ} → x ＝ y → Eq-ℚ x y
Eq-eq-ℚ {x} {.x} refl = refl-Eq-ℚ x

eq-Eq-ℚ : (x y : ℚ) → Eq-ℚ x y → x ＝ y
eq-Eq-ℚ x y H =
  equational-reasoning
    x
    ＝ rational-fraction-ℤ (fraction-ℚ x)
      by inv (is-retraction-rational-fraction-ℚ x)
    ＝ rational-fraction-ℤ (fraction-ℚ y)
      by eq-ℚ-sim-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H
    ＝ y by is-retraction-rational-fraction-ℚ y
```

## Properties

### Equality on the rationals is a proposition

```agda
abstract
  is-prop-Eq-ℚ : (x y : ℚ) → is-prop (Eq-ℚ x y)
  is-prop-Eq-ℚ x y = is-prop-sim-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

Eq-ℚ-Prop : (x y : ℚ) → Prop lzero
Eq-ℚ-Prop x y = (Eq-ℚ x y , is-prop-Eq-ℚ x y)
```

## The full characterization of the identity type of `ℚ`

```agda
abstract
  contraction-total-Eq-ℚ :
    (x : ℚ) (y : Σ ℚ (Eq-ℚ x)) → (x , refl-Eq-ℚ x) ＝ y
  contraction-total-Eq-ℚ x (y , e) =
    eq-pair-Σ (eq-Eq-ℚ x y e) (eq-is-prop (is-prop-Eq-ℚ x y))

abstract
  is-torsorial-Eq-ℚ : (x : ℚ) → is-torsorial (Eq-ℚ x)
  is-torsorial-Eq-ℚ x = ((x , refl-Eq-ℚ x) , contraction-total-Eq-ℚ x)

abstract
  is-equiv-Eq-eq-ℚ :
    (x y : ℚ) → is-equiv (Eq-eq-ℚ {x} {y})
  is-equiv-Eq-eq-ℚ x =
    fundamental-theorem-id (is-torsorial-Eq-ℚ x) (λ y → Eq-eq-ℚ {x} {y})

extensionality-ℚ : (x y : ℚ) → (x ＝ y) ≃ (Eq-ℚ x y)
extensionality-ℚ x y = (Eq-eq-ℚ , is-equiv-Eq-eq-ℚ x y)
```

### Equality on the rationals is decidable

```agda
has-decidable-equality-ℚ : has-decidable-equality ℚ
has-decidable-equality-ℚ =
  has-decidable-equality-Σ
    ( has-decidable-equality-fraction-ℤ)
    ( λ x → has-decidable-equality-is-prop (is-prop-is-reduced-fraction-ℤ x))
```
