# Truncated addition of truncation levels

```agda
module foundation.truncated-addition-truncation-levels where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inequality-truncation-levels
open import foundation.iterated-successors-truncation-levels
open import foundation.negated-equality
open import foundation.negation
open import foundation.truncation-levels
open import foundation.unit-type

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
```

</details>

## Idea

We define the
{{#concept "truncated addition" Disambiguation="of truncation levels" Agda=truncadd-𝕋}}
binary operation on [truncation levels](foundation-core.truncation-levels.md).
Truncated addition is given by interpreting truncation levels as
[integers](elementary-number-theory.integers.md),
[adding](elementary-number-theory.addition-integers.md) them together, and
interpreting the result as a truncation level again, mapping any result less
than -2 to -2.

**Note.** This operation, while conceptually clear, has many flaws that makes it
ill-equipped for use in formalization, and hence is not recommended. For
instance, the operation is not associative and does not reflect inequality. See
instead
[`iterated-successors-truncation-levels`](foundation.iterated-successors-truncation-levels.md)
for a more natural alternative.

## Definitions

### Truncated addition of truncation levels

```agda
truncadd-𝕋' : 𝕋 → 𝕋 → 𝕋
truncadd-𝕋' neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
truncadd-𝕋' neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
truncadd-𝕋' neg-two-𝕋 (succ-𝕋 (succ-𝕋 l)) = l
truncadd-𝕋' (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
truncadd-𝕋' (succ-𝕋 neg-two-𝕋) (succ-𝕋 l) = l
truncadd-𝕋' (succ-𝕋 (succ-𝕋 k)) neg-two-𝕋 = k
truncadd-𝕋' (succ-𝕋 (succ-𝕋 k)) (succ-𝕋 l) =
  succ-𝕋 (truncadd-𝕋' (succ-𝕋 k) (succ-𝕋 l))

truncadd-𝕋 : 𝕋 → 𝕋 → 𝕋
truncadd-𝕋 k r = truncadd-𝕋' r k
```

Agda is not happy with the following definition due to the `--exact-split` flag.

```text
truncadd-𝕋 : 𝕋 → 𝕋 → 𝕋
truncadd-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
truncadd-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
truncadd-𝕋 (succ-𝕋 (succ-𝕋 k)) neg-two-𝕋 = k
truncadd-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 neg-two-𝕋) = k
truncadd-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 r)) = r
truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 (succ-𝕋 r)) =
  succ-𝕋 (truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 r))
```

### The binary action of truncated addition on identifications

```agda
ap-binary-truncadd-𝕋 :
  {m n m' n' : 𝕋} → m ＝ m' → n ＝ n' → truncadd-𝕋 m n ＝ truncadd-𝕋 m' n'
ap-binary-truncadd-𝕋 p q = ap-binary truncadd-𝕋 p q
```

## Properties

### Unit laws for addition of truncation levels

```agda
left-unit-law-truncadd-𝕋 : (k : 𝕋) → truncadd-𝕋 zero-𝕋 k ＝ k
left-unit-law-truncadd-𝕋 neg-two-𝕋 = refl
left-unit-law-truncadd-𝕋 (succ-𝕋 neg-two-𝕋) = refl
left-unit-law-truncadd-𝕋 (succ-𝕋 (succ-𝕋 k)) =
  ap succ-𝕋 (left-unit-law-truncadd-𝕋 (succ-𝕋 k))

right-unit-law-truncadd-𝕋 : (k : 𝕋) → truncadd-𝕋 k zero-𝕋 ＝ k
right-unit-law-truncadd-𝕋 neg-two-𝕋 = refl
right-unit-law-truncadd-𝕋 (succ-𝕋 neg-two-𝕋) = refl
right-unit-law-truncadd-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) = refl
right-unit-law-truncadd-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 k))) = refl
```

### Successor laws for addition of truncation levels

```agda
right-successor-law-truncadd-𝕋 :
  (n k : 𝕋) →
  truncadd-𝕋 k (iterate-succ-𝕋 3 n) ＝ succ-𝕋 (truncadd-𝕋 k (iterate-succ-𝕋 2 n))
right-successor-law-truncadd-𝕋 n neg-two-𝕋 = refl
right-successor-law-truncadd-𝕋 n (succ-𝕋 k) = refl

left-successor-law-truncadd-𝕋 :
  (k n : 𝕋) →
  truncadd-𝕋 (iterate-succ-𝕋 3 n) k ＝ succ-𝕋 (truncadd-𝕋 (iterate-succ-𝕋 2 n) k)
left-successor-law-truncadd-𝕋 neg-two-𝕋 n = refl
left-successor-law-truncadd-𝕋 (succ-𝕋 neg-two-𝕋) n = refl
left-successor-law-truncadd-𝕋 (succ-𝕋 (succ-𝕋 k)) n =
  ap succ-𝕋 (left-successor-law-truncadd-𝕋 (succ-𝕋 k) n)
```

### The balancing law of the successor function over addition

```agda
balance-succ-truncadd-𝕋 :
  (k r : 𝕋) → truncadd-𝕋 (succ-𝕋 k) r ＝ truncadd-𝕋 k (succ-𝕋 r)
balance-succ-truncadd-𝕋 neg-two-𝕋 neg-two-𝕋 = refl
balance-succ-truncadd-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = refl
balance-succ-truncadd-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 r)) =
  ap succ-𝕋 (balance-succ-truncadd-𝕋 neg-two-𝕋 (succ-𝕋 r))
balance-succ-truncadd-𝕋 (succ-𝕋 k) neg-two-𝕋 = refl
balance-succ-truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 neg-two-𝕋) = refl
balance-succ-truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 (succ-𝕋 r)) =
  ap succ-𝕋 (balance-succ-truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 r))

abstract
  balance-iterated-succ-truncadd-𝕋 :
    (n : ℕ) (k r : 𝕋) →
    truncadd-𝕋 (iterate-succ-𝕋 n k) r ＝ truncadd-𝕋 k (iterate-succ-𝕋 n r)
  balance-iterated-succ-truncadd-𝕋 zero-ℕ k r = refl
  balance-iterated-succ-truncadd-𝕋 (succ-ℕ n) k r =
    ( balance-iterated-succ-truncadd-𝕋 n (succ-𝕋 k) r) ∙
    ( balance-succ-truncadd-𝕋 k (iterate-succ-𝕋 n r)) ∙
    ( ap (truncadd-𝕋 k) (inv (reassociate-iterate-succ-𝕋 n r)))
```

### The double successor of addition is the double successor of addition

```agda
abstract
  compute-succ-succ-truncadd-𝕋 :
    (k r : 𝕋) → add+2-𝕋 k r ＝ truncadd-𝕋 (succ-𝕋 (succ-𝕋 k)) r
  compute-succ-succ-truncadd-𝕋 k neg-two-𝕋 = refl
  compute-succ-succ-truncadd-𝕋 k (succ-𝕋 neg-two-𝕋) = refl
  compute-succ-succ-truncadd-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 r)) =
    left-unit-law-add+2-𝕋 (succ-𝕋 (succ-𝕋 r)) ∙
    inv (left-unit-law-truncadd-𝕋 (succ-𝕋 (succ-𝕋 r)))
  compute-succ-succ-truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 (succ-𝕋 r)) =
    ap succ-𝕋 (compute-succ-succ-truncadd-𝕋 (succ-𝕋 k) (succ-𝕋 r))

abstract
  compute-succ-succ-truncadd-𝕋' :
    (k r : 𝕋) → add+2-𝕋 k r ＝ truncadd-𝕋 k (succ-𝕋 (succ-𝕋 r))
  compute-succ-succ-truncadd-𝕋' k r =
    compute-succ-succ-truncadd-𝕋 k r ∙ balance-iterated-succ-truncadd-𝕋 2 k r
```

### Addition is not associative

```agda
example-not-associative-truncadd-𝕋 :
  truncadd-𝕋 (truncadd-𝕋 neg-two-𝕋 neg-two-𝕋) one-𝕋 ≠
  truncadd-𝕋 neg-two-𝕋 (truncadd-𝕋 neg-two-𝕋 one-𝕋)
example-not-associative-truncadd-𝕋 ()

not-associative-truncadd-𝕋 :
  ¬ ( (x y z : 𝕋) →
      truncadd-𝕋 (truncadd-𝕋 x y) z ＝ truncadd-𝕋 x (truncadd-𝕋 y z))
not-associative-truncadd-𝕋 α =
  example-not-associative-truncadd-𝕋 (α neg-two-𝕋 neg-two-𝕋 one-𝕋)
```

### Addition is commutative

```agda
abstract
  commutative-truncadd-𝕋 : (x y : 𝕋) → truncadd-𝕋 x y ＝ truncadd-𝕋 y x
  commutative-truncadd-𝕋 neg-two-𝕋 neg-two-𝕋 = refl
  commutative-truncadd-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = refl
  commutative-truncadd-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = refl
  commutative-truncadd-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = refl
  commutative-truncadd-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 neg-two-𝕋) = refl
  commutative-truncadd-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 (succ-𝕋 y)) =
    ap succ-𝕋 (commutative-truncadd-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y))
  commutative-truncadd-𝕋 (succ-𝕋 (succ-𝕋 x)) neg-two-𝕋 = refl
  commutative-truncadd-𝕋 (succ-𝕋 (succ-𝕋 x)) (succ-𝕋 neg-two-𝕋) =
    ap succ-𝕋 (commutative-truncadd-𝕋 (succ-𝕋 x) (succ-𝕋 neg-two-𝕋))
  commutative-truncadd-𝕋 (succ-𝕋 (succ-𝕋 x)) (succ-𝕋 (succ-𝕋 y)) =
    ap
      ( succ-𝕋)
      ( balance-succ-truncadd-𝕋 (succ-𝕋 x) (succ-𝕋 y) ∙
        commutative-truncadd-𝕋 (succ-𝕋 x) (succ-𝕋 (succ-𝕋 y)))
```

### Addition does not reflect inequality of truncation levels

```agda
example-not-reflects-leq-left-truncadd-𝕋 :
  (truncadd-𝕋 neg-one-𝕋 neg-two-𝕋) ≤-𝕋 (truncadd-𝕋 neg-two-𝕋 neg-two-𝕋) ×
  ¬ (neg-one-𝕋 ≤-𝕋 neg-two-𝕋)
example-not-reflects-leq-left-truncadd-𝕋 = (star , id)

not-reflects-leq-left-truncadd-𝕋 :
  ¬ ((k m n : 𝕋) → (truncadd-𝕋 m k) ≤-𝕋 (truncadd-𝕋 n k) → m ≤-𝕋 n)
not-reflects-leq-left-truncadd-𝕋 α = α neg-two-𝕋 neg-one-𝕋 neg-two-𝕋 star
```

### Coherence with addition on natural numbers

```agda
add+2-truncation-level-minus-one-ℕ :
  (k n : ℕ) →
  truncation-level-minus-one-ℕ (k +ℕ n) ＝
  add+2-𝕋
    ( truncation-level-minus-one-ℕ k)
    ( truncation-level-minus-two-ℕ n)
add+2-truncation-level-minus-one-ℕ k zero-ℕ = refl
add+2-truncation-level-minus-one-ℕ k (succ-ℕ n) =
  ap succ-𝕋 (add+2-truncation-level-minus-one-ℕ k n)
```

## See also

- [`iterated-successors-truncation-levels`](foundation.iterated-successors-truncation-levels.md)
