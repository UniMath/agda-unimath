# The large ring of complex numbers

```agda
module complex-numbers.large-ring-of-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.large-commutative-rings

open import complex-numbers.complex-numbers
open import complex-numbers.large-additive-group-of-complex-numbers
open import complex-numbers.multiplication-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.large-ring-of-real-numbers

open import ring-theory.large-rings
```

</details>

## Idea

The [complex numbers](complex-numbers.complex-numbers.md) form a
[large commutative ring](commutative-algebra.large-commutative-rings.md) under
[addition](complex-numbers.addition-complex-numbers.md) and
[multiplication](complex-numbers.multiplication-complex-numbers.md).

## Definition

```agda
large-ring-ℂ : Large-Ring lsuc (_⊔_)
large-ring-ℂ =
  make-Large-Ring
    ( large-ab-add-ℂ)
    ( mul-ℂ)
    ( λ _ _ z~z' _ _ → preserves-sim-mul-ℂ z~z')
    ( one-ℂ)
    ( associative-mul-ℂ)
    ( left-unit-law-mul-ℂ)
    ( right-unit-law-mul-ℂ)
    ( left-distributive-mul-add-ℂ)
    ( right-distributive-mul-add-ℂ)

large-commutative-ring-ℂ : Large-Commutative-Ring lsuc (_⊔_)
large-commutative-ring-ℂ =
  make-Large-Commutative-Ring
    ( large-ring-ℂ)
    ( commutative-mul-ℂ)
```

## Properties

### The commutative ring of complex numbers at a universe level

```agda
commutative-ring-ℂ : (l : Level) → Commutative-Ring (lsuc l)
commutative-ring-ℂ =
  commutative-ring-Large-Commutative-Ring large-commutative-ring-ℂ
```

### The canonical ring homomorphism from the real numbers to the complex numbers

```agda
hom-ring-ℝ-ℂ :
  (l : Level) →
  hom-Commutative-Ring (commutative-ring-ℝ l) (commutative-ring-ℂ l)
hom-ring-ℝ-ℂ l = (hom-ab-add-ℝ-ℂ l , inv (mul-complex-ℝ _ _) , refl)
```
