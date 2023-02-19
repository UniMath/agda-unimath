# Sums in commutative rings

```agda
module commutative-algebra.sums-commutative-rings where

open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors
open import linear-algebra.vectors-on-commutative-rings

open import univalent-combinatorics.standard-finite-types
```

## Definition

```agda
sum-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) (n : ℕ) →
  (functional-vec-Commutative-Ring R n) → type-Commutative-Ring R
sum-Commutative-Ring R zero-ℕ f = zero-Commutative-Ring R
sum-Commutative-Ring R (succ-ℕ n) f =
  add-Commutative-Ring R
    ( sum-Commutative-Ring R n (f ∘ inl-Fin n))
    ( f (inr star))
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where
  
  sum-one-element-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 1) →
    sum-Commutative-Ring R 1 f ＝ f (inr star)
  sum-one-element-Commutative-Ring f =
    left-unit-law-add-Commutative-Ring R (f (inr star))

  sum-two-elements-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 2) →
    sum-Commutative-Ring R 2 f ＝ add-Commutative-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Ring f =
    ( associative-add-Commutative-Ring R
      (zero-Commutative-Ring R) (f (zero-Fin 1)) (f (one-Fin 1))) ∙
    ( left-unit-law-add-Commutative-Ring R
      ( add-Commutative-Ring R (f (zero-Fin 1)) (f (one-Fin 1))))
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  htpy-sum-Commutative-Ring :
    (n : ℕ) {f g : functional-vec-Commutative-Ring R n} →
    (f ~ g) → sum-Commutative-Ring R n f ＝ sum-Commutative-Ring R n g
  htpy-sum-Commutative-Ring zero-ℕ H = refl
  htpy-sum-Commutative-Ring (succ-ℕ n) H =
    ap-binary
      ( add-Commutative-Ring R)
      ( htpy-sum-Commutative-Ring n (H ·r inl-Fin n)) (H (inr star))
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  cons-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    {x : type-Commutative-Ring R} → head-functional-vec n f ＝ x →
    sum-Commutative-Ring R (succ-ℕ n) f ＝
    add-Commutative-Ring R (sum-Commutative-Ring R n (f ∘ inl-Fin n)) x
  cons-sum-Commutative-Ring n f refl = refl

  snoc-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    {x : type-Commutative-Ring R} → f (zero-Fin n) ＝ x →
    sum-Commutative-Ring R (succ-ℕ n) f ＝
    add-Commutative-Ring R
      ( x)
      ( sum-Commutative-Ring R n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Ring zero-ℕ f refl =
    ( sum-one-element-Commutative-Ring R f) ∙
    ( inv (right-unit-law-add-Commutative-Ring R (f (zero-Fin 0))))
  snoc-sum-Commutative-Ring (succ-ℕ n) f refl =
    ( ap
      ( add-Commutative-Ring' R (head-functional-vec (succ-ℕ n) f))
      ( snoc-sum-Commutative-Ring n (f ∘ inl-Fin (succ-ℕ n)) refl)) ∙
    ( associative-add-Commutative-Ring R
      ( f (zero-Fin (succ-ℕ n)))
      ( sum-Commutative-Ring R n (f ∘ (inr-Fin (succ-ℕ n) ∘ inl-Fin n)))
      ( head-functional-vec (succ-ℕ n) f))
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R)
    (f : functional-vec-Commutative-Ring R n) →
    mul-Commutative-Ring R x (sum-Commutative-Ring R n f) ＝
    sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R x (f i))
  left-distributive-mul-sum-Commutative-Ring zero-ℕ x f =
    right-zero-law-mul-Commutative-Ring R x
  left-distributive-mul-sum-Commutative-Ring (succ-ℕ n) x f =
    ( left-distributive-mul-add-Commutative-Ring R x
      ( sum-Commutative-Ring R n (f ∘ inl-Fin n))
      ( f (inr star))) ∙
    ( ap
      ( add-Commutative-Ring' R (mul-Commutative-Ring R x (f (inr star))))
      ( left-distributive-mul-sum-Commutative-Ring n x (f ∘ inl-Fin n)))

  right-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R n)
    (x : type-Commutative-Ring R) →
    mul-Commutative-Ring R (sum-Commutative-Ring R n f) x ＝
    sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R (f i) x)
  right-distributive-mul-sum-Commutative-Ring zero-ℕ f x =
    left-zero-law-mul-Commutative-Ring R x
  right-distributive-mul-sum-Commutative-Ring (succ-ℕ n) f x =
    ( right-distributive-mul-add-Commutative-Ring R
      ( sum-Commutative-Ring R n (f ∘ inl-Fin n))
      ( f (inr star))
      ( x)) ∙
    ( ap
      ( add-Commutative-Ring' R (mul-Commutative-Ring R (f (inr star)) x))
      ( right-distributive-mul-sum-Commutative-Ring n (f ∘ inl-Fin n) x))
```

### Interchange law of sums and addition in commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  interchange-add-sum-Commutative-Ring :
    (n : ℕ) (f g : functional-vec-Commutative-Ring R n) →
    add-Commutative-Ring R
      ( sum-Commutative-Ring R n f)
      ( sum-Commutative-Ring R n g) ＝
    sum-Commutative-Ring R n
      ( add-functional-vec-Commutative-Ring R n f g)
  interchange-add-sum-Commutative-Ring zero-ℕ f g =
    left-unit-law-add-Commutative-Ring R (zero-Commutative-Ring R)
  interchange-add-sum-Commutative-Ring (succ-ℕ n) f g =
    ( interchange-add-add-Commutative-Ring R
      ( sum-Commutative-Ring R n (f ∘ inl-Fin n))
      ( f (inr star))
      ( sum-Commutative-Ring R n (g ∘ inl-Fin n))
      ( g (inr star))) ∙
    ( ap
      ( add-Commutative-Ring' R
        ( add-Commutative-Ring R (f (inr star)) (g (inr star))))
      ( interchange-add-sum-Commutative-Ring n
        ( f ∘ inl-Fin n)
        ( g ∘ inl-Fin n)))
    
```

### Extending a sum of elements in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  extend-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R n) →
    sum-Commutative-Ring R
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Ring R n (zero-Commutative-Ring R) f) ＝
    sum-Commutative-Ring R n f
  extend-sum-Commutative-Ring n f =
    right-unit-law-add-Commutative-Ring R (sum-Commutative-Ring R n f)
```

### Shifting a sum of elements in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  shift-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R n) →
    sum-Commutative-Ring R
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Ring R n f
        ( zero-Commutative-Ring R)) ＝
    sum-Commutative-Ring R n f
  shift-sum-Commutative-Ring zero-ℕ f =
    left-unit-law-add-Commutative-Ring R (zero-Commutative-Ring R)
  shift-sum-Commutative-Ring (succ-ℕ n) f =
    ap
      ( add-Commutative-Ring' R
        ( head-functional-vec-Commutative-Ring R n f))
      ( shift-sum-Commutative-Ring n
        ( tail-functional-vec-Commutative-Ring R n f))
```
