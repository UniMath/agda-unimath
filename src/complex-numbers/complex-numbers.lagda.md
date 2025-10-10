# Complex numbers

```agda
module complex-numbers.complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.gaussian-integers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "complex numbers" WDID=Q26851286 WD="set of complex numbers" Agda=ℂ}}
are numbers of the form `a + bi`, where `a` and `b` are
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
ℂ : (l : Level) → UU (lsuc l)
ℂ l = ℝ l × ℝ l

re-ℂ : {l : Level} → ℂ l → ℝ l
re-ℂ = pr1

im-ℂ : {l : Level} → ℂ l → ℝ l
im-ℂ = pr2
```

## Properties

### The set of complex numbers

```agda
ℂ-Set : (l : Level) → Set (lsuc l)
ℂ-Set l = product-Set (ℝ-Set l) (ℝ-Set l)

eq-ℂ :
  {l : Level} → {a b c d : ℝ l} → a ＝ c → b ＝ d → (a , b) ＝ (c , d)
eq-ℂ = eq-pair
```

### The canonical embedding of real numbers into the complex numbers

```agda
complex-ℝ : {l : Level} → ℝ l → ℂ l
complex-ℝ {l} a = (a , raise-ℝ l zero-ℝ)
```

### The imaginary embedding of real numbers into the complex numbers

```agda
im-complex-ℝ : {l : Level} → ℝ l → ℂ l
im-complex-ℝ {l} a = (raise-ℝ l zero-ℝ , a)
```

### The canonical embedding of Gaussian integers into the complex numbers

```agda
complex-ℤ[i] : ℤ[i] → ℂ lzero
complex-ℤ[i] (a , b) = (real-ℤ a , real-ℤ b)
```

### The conjugate of a complex number

```agda
conjugate-ℂ : {l : Level} → ℂ l → ℂ l
conjugate-ℂ (a , b) = (a , neg-ℝ b)
```

### Important complex numbers

```agda
zero-ℂ : ℂ lzero
zero-ℂ = (zero-ℝ , zero-ℝ)

one-ℂ : ℂ lzero
one-ℂ = (one-ℝ , zero-ℝ)

neg-one-ℂ : ℂ lzero
neg-one-ℂ = (neg-one-ℝ , zero-ℝ)

i-ℂ : ℂ lzero
i-ℂ = (zero-ℝ , one-ℝ)
```

### Negation of complex numbers

```agda
neg-ℂ : {l : Level} → ℂ l → ℂ l
neg-ℂ (a , b) = (neg-ℝ a , neg-ℝ b)
```
