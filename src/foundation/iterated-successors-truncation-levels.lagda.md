# Iterated successors of truncation levels

```agda
module foundation.iterated-successors-truncation-levels where
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

We define the
{{#concept "truncated addition" Disambiguation="of truncation levels" Agda=truncadd-𝕋}}
binary operation on [truncation levels](foundation-core.truncation-levels.md).

## Definitions

### The double successor of addition on truncation levels

```agda
add+2-𝕋 : 𝕋 → 𝕋 → 𝕋
add+2-𝕋 x neg-two-𝕋 = x
add+2-𝕋 x (succ-𝕋 y) = succ-𝕋 (add+2-𝕋 x y)
```

### The binary action of truncated addition on identifications

```agda
ap-binary-add+2-𝕋 :
  {m n m' n' : 𝕋} → m ＝ m' → n ＝ n' → add+2-𝕋 m n ＝ add+2-𝕋 m' n'
ap-binary-add+2-𝕋 p = ap-binary add+2-𝕋 p
```

## Properties

### Unit laws for addition of truncation levels

```agda
left-unit-law-add+2-𝕋 : (k : 𝕋) → add+2-𝕋 neg-two-𝕋 k ＝ k
left-unit-law-add+2-𝕋 neg-two-𝕋 = refl
left-unit-law-add+2-𝕋 (succ-𝕋 k) =
  ap succ-𝕋 (left-unit-law-add+2-𝕋 k)

right-unit-law-add+2-𝕋 : (k : 𝕋) → add+2-𝕋 k neg-two-𝕋 ＝ k
right-unit-law-add+2-𝕋 neg-two-𝕋 = refl
right-unit-law-add+2-𝕋 (succ-𝕋 k) = refl
```

### Successor laws for the double successor of addition of truncation levels

```agda
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
balance-succ-add+2-𝕋 : (k r : 𝕋) → add+2-𝕋 (succ-𝕋 k) r ＝ add+2-𝕋 k (succ-𝕋 r)
balance-succ-add+2-𝕋 neg-two-𝕋 neg-two-𝕋 = refl
balance-succ-add+2-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = refl
balance-succ-add+2-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 r)) =
  ap succ-𝕋 (balance-succ-add+2-𝕋 neg-two-𝕋 (succ-𝕋 r))
balance-succ-add+2-𝕋 (succ-𝕋 k) neg-two-𝕋 = refl
balance-succ-add+2-𝕋 (succ-𝕋 k) (succ-𝕋 neg-two-𝕋) = refl
balance-succ-add+2-𝕋 (succ-𝕋 k) (succ-𝕋 (succ-𝕋 r)) =
  ap succ-𝕋 (balance-succ-add+2-𝕋 (succ-𝕋 k) (succ-𝕋 r))

abstract
  balance-iterated-succ-add+2-𝕋 :
    (n : ℕ) (k r : 𝕋) →
    add+2-𝕋 (iterate-succ-𝕋 n k) r ＝ add+2-𝕋 k (iterate-succ-𝕋 n r)
  balance-iterated-succ-add+2-𝕋 zero-ℕ k r = refl
  balance-iterated-succ-add+2-𝕋 (succ-ℕ n) k r =
    ( balance-iterated-succ-add+2-𝕋 n (succ-𝕋 k) r) ∙
    ( balance-succ-add+2-𝕋 k (iterate-succ-𝕋 n r)) ∙
    ( ap (add+2-𝕋 k) (inv (reassociate-iterate-succ-𝕋 n r)))
```

### The double successor of addition is commutative

```agda
-- abstract
--   commutative-add+2-𝕋 : (x y : 𝕋) → add+2-𝕋 x y ＝ add+2-𝕋 y x
--   commutative-add+2-𝕋 = ?
  -- commutative-add+2-𝕋 neg-two-𝕋 neg-two-𝕋 = refl
  -- commutative-add+2-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = refl
  -- commutative-add+2-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = {!   !}
  -- commutative-add+2-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = refl
  -- commutative-add+2-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 neg-two-𝕋) = refl
  -- commutative-add+2-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 (succ-𝕋 y)) =
  --   ap succ-𝕋 (commutative-add+2-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y))
  -- commutative-add+2-𝕋 (succ-𝕋 (succ-𝕋 x)) neg-two-𝕋 = {!   !}
  -- commutative-add+2-𝕋 (succ-𝕋 (succ-𝕋 x)) (succ-𝕋 neg-two-𝕋) =
  --   ap succ-𝕋 (commutative-add+2-𝕋 (succ-𝕋 x) (succ-𝕋 neg-two-𝕋))
  -- commutative-add+2-𝕋 (succ-𝕋 (succ-𝕋 x)) (succ-𝕋 (succ-𝕋 y)) =
  --   ap
  --     ( succ-𝕋)
  --     ( balance-succ-add+2-𝕋 (succ-𝕋 x) (succ-𝕋 y) ∙
  --       commutative-add+2-𝕋 (succ-𝕋 x) (succ-𝕋 (succ-𝕋 y)))
```
