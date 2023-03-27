# Divisibility of natural numbers

```agda
module elementary-number-theory.divisibility-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equational-reasoning
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.universe-levels
```

</details>

# Divisibility on the natural numbers

```agda
div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → mul-ℕ k m ＝ n)

quotient-div-ℕ : (x y : ℕ) → div-ℕ x y → ℕ
quotient-div-ℕ x y H = pr1 H

eq-quotient-div-ℕ :
  (x y : ℕ) (H : div-ℕ x y) → mul-ℕ (quotient-div-ℕ x y H) x ＝ y
eq-quotient-div-ℕ x y H = pr2 H

eq-quotient-div-ℕ' :
  (x y : ℕ) (H : div-ℕ x y) → mul-ℕ x (quotient-div-ℕ x y H) ＝ y
eq-quotient-div-ℕ' x y H =
  commutative-mul-ℕ x (quotient-div-ℕ x y H) ∙ eq-quotient-div-ℕ x y H

concatenate-eq-div-ℕ :
  {x y z : ℕ} → x ＝ y → div-ℕ y z → div-ℕ x z
concatenate-eq-div-ℕ refl p = p

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → y ＝ z → div-ℕ x z
concatenate-div-eq-ℕ p refl = p

concatenate-eq-div-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → div-ℕ y z → z ＝ w → div-ℕ x w
concatenate-eq-div-eq-ℕ refl p refl = p
```

## Properties

### Divisibility by a nonzero natural number is a property

```agda
is-prop-div-ℕ : (k x : ℕ) → is-nonzero-ℕ k → is-prop (div-ℕ k x)
is-prop-div-ℕ k x f = is-prop-map-is-emb (is-emb-mul-ℕ' k f) x
```

### The divisibility relation is a partial order on the natural numbers

```agda
refl-div-ℕ : (x : ℕ) → div-ℕ x x
pr1 (refl-div-ℕ x) = 1
pr2 (refl-div-ℕ x) = left-unit-law-mul-ℕ x

div-eq-ℕ : (x y : ℕ) → x ＝ y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x

antisymmetric-div-ℕ :
  (x y : ℕ) → div-ℕ x y → div-ℕ y x → x ＝ y
antisymmetric-div-ℕ zero-ℕ zero-ℕ H K = refl
antisymmetric-div-ℕ zero-ℕ (succ-ℕ y) (pair k p) K =
  inv (right-zero-law-mul-ℕ k) ∙ p
antisymmetric-div-ℕ (succ-ℕ x) zero-ℕ H (pair l q) =
  inv q ∙ right-zero-law-mul-ℕ l
antisymmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (pair k p) (pair l q) =
  ( inv (left-unit-law-mul-ℕ (succ-ℕ x))) ∙
  ( ( ap ( mul-ℕ' (succ-ℕ x))
         ( inv
           ( is-one-right-is-one-mul-ℕ l k
             ( is-one-is-left-unit-mul-ℕ (mul-ℕ l k) x
               ( ( associative-mul-ℕ l k (succ-ℕ x)) ∙
                 ( ap (mul-ℕ l) p ∙ q)))))) ∙
    ( p))

transitive-div-ℕ :
  (x y z : ℕ) → div-ℕ x y → div-ℕ y z → div-ℕ x z
pr1 (transitive-div-ℕ x y z (pair k p) (pair l q)) = mul-ℕ l k
pr2 (transitive-div-ℕ x y z (pair k p) (pair l q)) =
  associative-mul-ℕ l k x ∙ (ap (mul-ℕ l) p ∙ q)
```

### If `x` is nonzero and `d | x`, then `d ≤ x`

```agda
leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
... | (pair y refl) = leq-div-succ-ℕ d y H
```

### If `x` is nonzero, if `d | x` and `d ≠ x`, then `d < x`

```agda
le-div-succ-ℕ :
  (d x : ℕ) → div-ℕ d (succ-ℕ x) → ¬ (d ＝ succ-ℕ x) → le-ℕ d (succ-ℕ x)
le-div-succ-ℕ d x H f = le-leq-neq-ℕ (leq-div-succ-ℕ d x H) f

le-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → ¬ (d ＝ x) → le-ℕ d x
le-div-ℕ d x H K f = le-leq-neq-ℕ (leq-div-ℕ d x H K) f
```

### `1` divides any number

```agda
div-one-ℕ :
  (x : ℕ) → div-ℕ 1 x
pr1 (div-one-ℕ x) = x
pr2 (div-one-ℕ x) = right-unit-law-mul-ℕ x

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .1 x refl = div-one-ℕ x
```

### `x | 1` implies `x ＝ 1`

```agda
is-one-div-one-ℕ : (x : ℕ) → div-ℕ x 1 → is-one-ℕ x
is-one-div-one-ℕ x H = antisymmetric-div-ℕ x 1 H (div-one-ℕ x)
```

### Any number divides `0`

```agda
div-zero-ℕ :
  (k : ℕ) → div-ℕ k 0
pr1 (div-zero-ℕ k) = 0
pr2 (div-zero-ℕ k) = left-zero-law-mul-ℕ k

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = div-zero-ℕ k
```

### `0 | x` implies `x = 0` and `x | 1` implies `x = 1`

```agda
is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = antisymmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d
```

### Any divisor of a nonzero number is nonzero

```agda
is-nonzero-div-ℕ :
  (k x : ℕ) → div-ℕ k x → is-nonzero-ℕ x → is-nonzero-ℕ k
is-nonzero-div-ℕ .zero-ℕ x H K refl = K (is-zero-div-zero-ℕ x H)
```

### If `x < d` and `d | x`, then `x` must be `0`

```agda
is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (mul-ℕ k d)) p))
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (mul-ℕ k y)
div-mul-ℕ k x y H =
  transitive-div-ℕ x y (mul-ℕ k y) H (pair k refl)

div-mul-ℕ' :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (mul-ℕ y k)
div-mul-ℕ' k x y H =
  tr (div-ℕ x) (commutative-mul-ℕ k y) (div-mul-ℕ k x y H)
```

### A 3-for-2 property of division with respect to addition

```agda
div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
pr1 (div-add-ℕ d x y (pair n p) (pair m q)) = add-ℕ n m
pr2 (div-add-ℕ d x y (pair n p) (pair m q)) =
  ( right-distributive-mul-add-ℕ n m d) ∙
  ( ap-add-ℕ p q)

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
pr1 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) = dist-ℕ m n
pr2 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) =
  is-injective-add-ℕ' (mul-ℕ m (succ-ℕ d))
    ( ( inv
        ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
          ( commutative-add-ℕ
            ( mul-ℕ m (succ-ℕ d))
            ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙
      ( ( ap
          ( mul-ℕ' (succ-ℕ d))
          ( is-additive-right-inverse-dist-ℕ m n
            ( reflects-order-mul-ℕ d m n
              ( concatenate-eq-leq-eq-ℕ q
                ( leq-add-ℕ' y x)
                ( inv p))))) ∙
        ( p ∙ (ap (add-ℕ x) (inv q)))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))
```

### If `d` divides both `x` and `x + 1`, then `d ＝ 1`

```agda
is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y 1 H K)
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ (mul-ℕ k x) (mul-ℕ k y)
pr1 (preserves-div-mul-ℕ k x y (pair q p)) = q
pr2 (preserves-div-mul-ℕ k x y (pair q p)) =
  ( inv (associative-mul-ℕ q k x)) ∙
    ( ( ap (mul-ℕ' x) (commutative-mul-ℕ q k)) ∙
      ( ( associative-mul-ℕ k q x) ∙
        ( ap (mul-ℕ k) p)))
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℕ :
  (k x y : ℕ) → is-nonzero-ℕ k → div-ℕ (mul-ℕ k x) (mul-ℕ k y) → div-ℕ x y
pr1 (reflects-div-mul-ℕ k x y H (pair q p)) = q
pr2 (reflects-div-mul-ℕ k x y H (pair q p)) =
  is-injective-mul-ℕ k H
    ( ( inv (associative-mul-ℕ k q x)) ∙
      ( ( ap (mul-ℕ' x) (commutative-mul-ℕ k q)) ∙
        ( ( associative-mul-ℕ q k x) ∙
          ( p))))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`.

```agda
div-quotient-div-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) → is-nonzero-ℕ d →
  div-ℕ (mul-ℕ d x) y → div-ℕ x (quotient-div-ℕ d y H)
div-quotient-div-div-ℕ x y d H f K =
  reflects-div-mul-ℕ d x
    ( quotient-div-ℕ d y H)
    ( f)
    ( tr (div-ℕ (mul-ℕ d x)) (inv (eq-quotient-div-ℕ' d y H)) K)

div-div-quotient-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) →
  div-ℕ x (quotient-div-ℕ d y H) → div-ℕ (mul-ℕ d x) y
div-div-quotient-div-ℕ x y d H K =
  tr ( div-ℕ (mul-ℕ d x))
     ( eq-quotient-div-ℕ' d y H)
     ( preserves-div-mul-ℕ d x (quotient-div-ℕ d y H) K)
```

### If `d` divides a nonzero number `x`, then the quotient `x/d` is also nonzero

```agda
is-nonzero-quotient-div-ℕ :
  {d x : ℕ} (H : div-ℕ d x) →
  is-nonzero-ℕ x → is-nonzero-ℕ (quotient-div-ℕ d x H)
is-nonzero-quotient-div-ℕ {d} {.(mul-ℕ k d)} (pair k refl) =
  is-nonzero-left-factor-mul-ℕ k d
```

### `a/a ＝ 1`

```agda
is-idempotent-quotient-div-ℕ :
  (a : ℕ) → is-nonzero-ℕ a → (H : div-ℕ a a) → is-one-ℕ (quotient-div-ℕ a a H)
is-idempotent-quotient-div-ℕ zero-ℕ nz (u , p) = ex-falso (nz refl)
is-idempotent-quotient-div-ℕ (succ-ℕ a) nz (u , p) =
  is-one-is-left-unit-mul-ℕ u a p
```

### If `b` divides `a` and `c` divides `b` and `c` is nonzero, then `a/b · b/c ＝ a/c`

```agda
simplify-mul-quotient-div-ℕ :
  {a b c : ℕ}  → is-nonzero-ℕ c →
  (H : div-ℕ b a) (K : div-ℕ c b) (L : div-ℕ c a) →
  ( mul-ℕ (quotient-div-ℕ b a H) (quotient-div-ℕ c b K)) ＝
  ( quotient-div-ℕ c a L)
simplify-mul-quotient-div-ℕ {a} {b} {c} nz H K L =
  is-injective-mul-ℕ' c nz
    ( equational-reasoning
      mul-ℕ (mul-ℕ a/b b/c) c
      ＝ mul-ℕ a/b (mul-ℕ b/c c)   by associative-mul-ℕ a/b b/c c
      ＝ mul-ℕ a/b b               by ap (mul-ℕ a/b) (eq-quotient-div-ℕ c b K)
      ＝ a                         by eq-quotient-div-ℕ b a H
      ＝ mul-ℕ a/c c               by inv (eq-quotient-div-ℕ c a L))
  where
  a/b : ℕ
  a/b = quotient-div-ℕ b a H
  b/c : ℕ
  b/c = quotient-div-ℕ c b K
  a/c : ℕ
  a/c = quotient-div-ℕ c a L
```

### If `d | a` and `d` is nonzero, then `x | a/d` if and only if `xd | a`

```agda
simplify-div-quotient-div-ℕ :
  {a d x : ℕ} → is-nonzero-ℕ d → (H : div-ℕ d a) →
  (div-ℕ x (quotient-div-ℕ d a H)) ↔ (div-ℕ (mul-ℕ x d) a)
pr1 (pr1 (simplify-div-quotient-div-ℕ nz H) (u , p)) = u
pr2 (pr1 (simplify-div-quotient-div-ℕ {a} {d} {x} nz H) (u , p)) =
  equational-reasoning
    mul-ℕ u (mul-ℕ x d)
    ＝ mul-ℕ (mul-ℕ u x) d                 by inv (associative-mul-ℕ u x d)
    ＝ mul-ℕ (quotient-div-ℕ d a H) d      by ap (mul-ℕ' d) p
    ＝ a                                   by eq-quotient-div-ℕ d a H
pr1 (pr2 (simplify-div-quotient-div-ℕ nz H) (u , p)) = u
pr2 (pr2 (simplify-div-quotient-div-ℕ {a} {d} {x} nz H) (u , p)) =
  is-injective-mul-ℕ' d nz
    ( equational-reasoning
        mul-ℕ (mul-ℕ u x) d
        ＝ mul-ℕ u (mul-ℕ x d)             by associative-mul-ℕ u x d
        ＝ a                               by p
        ＝ mul-ℕ (quotient-div-ℕ d a H) d  by inv (eq-quotient-div-ℕ d a H))
```

### Suppose `H : b | a` and `K : c | b`, where `c` is nonzero`. If `d`divides`b/c`then`d`divides`a/c`.

```agda
div-quotient-div-div-quotient-div-ℕ :
  {a b c d : ℕ} → is-nonzero-ℕ c → (H : div-ℕ b a)
  (K : div-ℕ c b) (L : div-ℕ c a) →
  div-ℕ d (quotient-div-ℕ c b K) →
  div-ℕ d (quotient-div-ℕ c a L)
div-quotient-div-div-quotient-div-ℕ {a} {b} {c} {d} nz H K L M =
  tr
    ( div-ℕ d)
    ( simplify-mul-quotient-div-ℕ nz H K L)
    ( div-mul-ℕ
      ( quotient-div-ℕ b a H)
      ( d)
      ( quotient-div-ℕ c b K)
      ( M))
```
