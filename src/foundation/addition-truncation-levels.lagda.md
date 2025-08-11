# Addition of truncation levels

```agda
module foundation.addition-truncation-levels where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.truncation-levels
```

</details>

## Idea

We define the partial
{{#concept "addition" Disambiguation="of truncation levels" Agda=add-𝕋 Agda=_+𝕋_}}
binary operation on [truncation levels](foundation-core.truncation-levels.md).

## Definitions

### Addition of truncation levels

```agda
add-𝕋' : 𝕋 → 𝕋 → 𝕋
add-𝕋' neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋' neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋' neg-two-𝕋 (succ-𝕋 (succ-𝕋 l)) = l
add-𝕋' (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋' (succ-𝕋 neg-two-𝕋) (succ-𝕋 l) = l
add-𝕋' (succ-𝕋 (succ-𝕋 k)) neg-two-𝕋 = k
add-𝕋' (succ-𝕋 (succ-𝕋 k)) (succ-𝕋 l) = succ-𝕋 (add-𝕋' (succ-𝕋 k) (succ-𝕋 l))

add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 k r = add-𝕋' r k
```

Agda is not happy with the following definition due to the `--exact-split` flag.

```text
add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 (succ-𝕋 k)) neg-two-𝕋 = k
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋 (succ-𝕋 k) (succ-𝕋 neg-two-𝕋) = k
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 r)) = r
add-𝕋 (succ-𝕋 k) (succ-𝕋 (succ-𝕋 r)) = succ-𝕋 (add-𝕋 (succ-𝕋 k) (succ-𝕋 r))
```

```agda
infixl 35 _+𝕋_
_+𝕋_ = add-𝕋
```

### The double successor of addition on truncation levels

```agda
add+2-𝕋 : 𝕋 → 𝕋 → 𝕋
add+2-𝕋 x neg-two-𝕋 = x
add+2-𝕋 x (succ-𝕋 y) = succ-𝕋 (add+2-𝕋 x y)
```

```agda
ap-add-𝕋 : {m n m' n' : 𝕋} → m ＝ m' → n ＝ n' → m +𝕋 n ＝ m' +𝕋 n'
ap-add-𝕋 p q = ap-binary add-𝕋 p q
```

## Properties

### Unit laws for addition of truncation levels

```agda
left-unit-law-add-𝕋 : (k : 𝕋) → zero-𝕋 +𝕋 k ＝ k
left-unit-law-add-𝕋 neg-two-𝕋 = refl
left-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = refl
left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 k)) =
  ap succ-𝕋 (left-unit-law-add-𝕋 (succ-𝕋 k))

right-unit-law-add-𝕋 : (k : 𝕋) → k +𝕋 zero-𝕋 ＝ k
right-unit-law-add-𝕋 neg-two-𝕋 = refl
right-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = refl
right-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) = refl
right-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 k))) = refl

left-unit-law-add+2-𝕋 : (k : 𝕋) → add+2-𝕋 neg-two-𝕋 k ＝ k
left-unit-law-add+2-𝕋 neg-two-𝕋 = refl
left-unit-law-add+2-𝕋 (succ-𝕋 k) =
  ap succ-𝕋 (left-unit-law-add+2-𝕋 k)

right-unit-law-add+2-𝕋 : (k : 𝕋) → add+2-𝕋 k neg-two-𝕋 ＝ k
right-unit-law-add+2-𝕋 neg-two-𝕋 = refl
right-unit-law-add+2-𝕋 (succ-𝕋 k) = refl
```

### Successor laws for addition of truncation levels

```agda
right-successor-law-add-𝕋 :
  (n k : 𝕋) → k +𝕋 iterated-succ-𝕋 3 n ＝ succ-𝕋 (k +𝕋 iterated-succ-𝕋 2 n)
right-successor-law-add-𝕋 n neg-two-𝕋 = refl
right-successor-law-add-𝕋 n (succ-𝕋 k) = refl

left-successor-law-add-𝕋 :
  (k n : 𝕋) → iterated-succ-𝕋 3 n +𝕋 k ＝ succ-𝕋 (iterated-succ-𝕋 2 n +𝕋 k)
left-successor-law-add-𝕋 neg-two-𝕋 n = refl
left-successor-law-add-𝕋 (succ-𝕋 neg-two-𝕋) n = refl
left-successor-law-add-𝕋 (succ-𝕋 (succ-𝕋 k)) n =
  ap succ-𝕋 (left-successor-law-add-𝕋 (succ-𝕋 k) n)

right-successor-law-add+2-𝕋 :
  (n k : 𝕋) → add+2-𝕋 k (succ-𝕋 n) ＝ succ-𝕋 (add+2-𝕋 k n)
right-successor-law-add+2-𝕋 n k = refl

left-successor-law-add+2-𝕋 :
  (n k : 𝕋) → add+2-𝕋 (succ-𝕋 k) n ＝ succ-𝕋 (add+2-𝕋 k n)
left-successor-law-add+2-𝕋 neg-two-𝕋 n = refl
left-successor-law-add+2-𝕋 (succ-𝕋 k) n =
  ap succ-𝕋 (left-successor-law-add+2-𝕋 k n)
```

### The balancing law of the successor function over addition

```agda
balance-succ-add-𝕋 : (k r : 𝕋) → succ-𝕋 k +𝕋 r ＝ k +𝕋 succ-𝕋 r
balance-succ-add-𝕋 neg-two-𝕋 neg-two-𝕋 = refl
balance-succ-add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = refl
balance-succ-add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 r)) =
  ap succ-𝕋 (balance-succ-add-𝕋 neg-two-𝕋 (succ-𝕋 r))
balance-succ-add-𝕋 (succ-𝕋 k) neg-two-𝕋 = refl
balance-succ-add-𝕋 (succ-𝕋 k) (succ-𝕋 neg-two-𝕋) = refl
balance-succ-add-𝕋 (succ-𝕋 k) (succ-𝕋 (succ-𝕋 r)) =
  ap succ-𝕋 (balance-succ-add-𝕋 (succ-𝕋 k) (succ-𝕋 r))

abstract
  balance-iterated-succ-add-𝕋 :
    (n : ℕ) (k r : 𝕋) → iterated-succ-𝕋 n k +𝕋 r ＝ k +𝕋 iterated-succ-𝕋 n r
  balance-iterated-succ-add-𝕋 zero-ℕ k r = refl
  balance-iterated-succ-add-𝕋 (succ-ℕ n) k r =
    ( balance-iterated-succ-add-𝕋 n (succ-𝕋 k) r) ∙
    ( balance-succ-add-𝕋 k (iterated-succ-𝕋 n r)) ∙
    ( ap (k +𝕋_) (inv (reassociate-iterated-succ-𝕋 n r)))
```

### The double successor of addition is the double successor of addition

```agda
abstract
  compute-add+2-𝕋 :
    (k r : 𝕋) → add+2-𝕋 k r ＝ iterated-succ-𝕋 2 k +𝕋 r
  compute-add+2-𝕋 k neg-two-𝕋 = refl
  compute-add+2-𝕋 k (succ-𝕋 neg-two-𝕋) = refl
  compute-add+2-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 r)) =
    left-unit-law-add+2-𝕋 (succ-𝕋 (succ-𝕋 r)) ∙
    inv (left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 r)))
  compute-add+2-𝕋 (succ-𝕋 k) (succ-𝕋 (succ-𝕋 r)) =
    ap succ-𝕋 (compute-add+2-𝕋 (succ-𝕋 k) (succ-𝕋 r))

abstract
  compute-add+2-𝕋' :
    (k r : 𝕋) → add+2-𝕋 k r ＝ k +𝕋 iterated-succ-𝕋 2 r
  compute-add+2-𝕋' k r = compute-add+2-𝕋 k r ∙ balance-iterated-succ-add-𝕋 2 k r
```

### Addition is not associative

```agda
example-not-associative-add-𝕋 :
  (neg-two-𝕋 +𝕋 neg-two-𝕋) +𝕋 one-𝕋 ≠ neg-two-𝕋 +𝕋 (neg-two-𝕋 +𝕋 one-𝕋)
example-not-associative-add-𝕋 ()

not-associative-add-𝕋 : ¬ ((x y z : 𝕋) → (x +𝕋 y) +𝕋 z ＝ x +𝕋 (y +𝕋 z))
not-associative-add-𝕋 α =
  example-not-associative-add-𝕋 (α neg-two-𝕋 neg-two-𝕋 one-𝕋)
```

### Addition is commutative

```agda
abstract
  commutative-add-𝕋 : (x y : 𝕋) → x +𝕋 y ＝ y +𝕋 x
  commutative-add-𝕋 neg-two-𝕋 neg-two-𝕋 = refl
  commutative-add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = refl
  commutative-add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = refl
  commutative-add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = refl
  commutative-add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 neg-two-𝕋) = refl
  commutative-add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 (succ-𝕋 y)) =
    ap succ-𝕋 (commutative-add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y))
  commutative-add-𝕋 (succ-𝕋 (succ-𝕋 x)) neg-two-𝕋 = refl
  commutative-add-𝕋 (succ-𝕋 (succ-𝕋 x)) (succ-𝕋 neg-two-𝕋) =
    ap succ-𝕋 (commutative-add-𝕋 (succ-𝕋 x) (succ-𝕋 neg-two-𝕋))
  commutative-add-𝕋 (succ-𝕋 (succ-𝕋 x)) (succ-𝕋 (succ-𝕋 y)) =
    ap
      ( succ-𝕋)
      ( balance-succ-add-𝕋 (succ-𝕋 x) (succ-𝕋 y) ∙
        commutative-add-𝕋 (succ-𝕋 x) (succ-𝕋 (succ-𝕋 y)))
```
