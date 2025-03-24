# The Jacobi symbol

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.jacobi-symbol
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic funext univalence truncations
open import elementary-number-theory.integers
open import elementary-number-theory.legendre-symbol funext univalence truncations
open import elementary-number-theory.multiplication-integers funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.type-arithmetic-dependent-function-types funext univalence
open import foundation.unit-type

open import lists.functoriality-lists funext univalence truncations
open import lists.lists
```

</details>

## Idea

The
{{#concept "Jacobi symbol" WD="Jacobi symbol" WDID=Q241015 Agda=jacobi-symbol}}
is a function which encodes information about the
[squareness](elementary-number-theory.squares-modular-arithmetic.md) of an
[integer](elementary-number-theory.integers.md) within certain
[rings of integers modulo `p`](elementary-number-theory.modular-arithmetic.md),
for [prime](elementary-number-theory.prime-numbers.md) `p`. Specifically,
`jacobi-symbol(a,n)` for an integer `a : ℤ` and natural number `n : ℕ` is the
product of the [legendre symbols](elementary-number-theory.legendre-symbol.md)

```text
  legendre-symbol(p₁,a) · legendre-symbol(p₂,a) · … · legendre-symbol(pₖ,a),
```

where `p₁, …, pₖ` are the prime factors of `n`, not necessarily distinct (i.e.
it is possible that `pᵢ = pⱼ`).

## Definition

```agda
jacobi-symbol : ℤ → ℕ → ℤ
jacobi-symbol a 0 = zero-ℤ
jacobi-symbol a 1 = one-ℤ
jacobi-symbol a (succ-ℕ (succ-ℕ n)) =
  fold-list
    ( one-ℤ)
    ( mul-ℤ)
    ( map-list
      ( swap-Π legendre-symbol a)
      ( list-primes-fundamental-theorem-arithmetic-ℕ (succ-ℕ (succ-ℕ n)) star))
```
