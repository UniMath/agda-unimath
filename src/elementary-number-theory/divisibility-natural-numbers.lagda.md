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

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
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

is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ 2 n

is-odd-ℕ : ℕ → UU lzero
is-odd-ℕ n = ¬ (is-even-ℕ n)

div-one-ℕ :
  (x : ℕ) → div-ℕ 1 x
pr1 (div-one-ℕ x) = x
pr2 (div-one-ℕ x) = right-unit-law-mul-ℕ x

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .1 x refl = div-one-ℕ x

div-zero-ℕ :
  (k : ℕ) → div-ℕ k 0
pr1 (div-zero-ℕ k) = 0
pr2 (div-zero-ℕ k) = left-zero-law-mul-ℕ k

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = div-zero-ℕ k
```

## Divisibility by a nonzero natural number is a property

```agda
is-prop-div-ℕ : (k x : ℕ) → is-nonzero-ℕ k → is-prop (div-ℕ k x)
is-prop-div-ℕ k x f = is-prop-map-is-emb (is-emb-mul-ℕ' k f) x
```

## A three-for-two property of division

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
            ( leq-leq-mul-ℕ' m n d
              ( concatenate-eq-leq-eq-ℕ q
                ( leq-add-ℕ' y x)
                ( inv p))))) ∙
        ( p ∙ (ap (add-ℕ x) (inv q)))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))
```

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

### The divisibility relation is a partial order on the natural numbers

```agda
refl-div-ℕ : (x : ℕ) → div-ℕ x x
pr1 (refl-div-ℕ x) = 1
pr2 (refl-div-ℕ x) = left-unit-law-mul-ℕ x

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

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (mul-ℕ k y)
div-mul-ℕ k x y H =
  transitive-div-ℕ x y (mul-ℕ k y) H (pair k refl)
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

### `0 | x` implies `x = 0` and `x | 1` implies `x = 1`

```agda
is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = antisymmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d

is-one-div-one-ℕ : (x : ℕ) → div-ℕ x 1 → is-one-ℕ x
is-one-div-one-ℕ x H = antisymmetric-div-ℕ x 1 H (div-one-ℕ x)

is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y 1 H K)

div-eq-ℕ : (x y : ℕ) → x ＝ y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x
```

```agda
leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
... | (pair y refl) = leq-div-succ-ℕ d y H
```

```agda
is-one-is-divisor-below-ℕ : ℕ → ℕ → UU lzero
is-one-is-divisor-below-ℕ n a =
  (x : ℕ) → leq-ℕ x n → div-ℕ x a → is-one-ℕ x
```

### If `d` divides a nonzero number `x`, then the quotient `x/d` is also nonzero

```agda
is-nonzero-quotient-div-ℕ :
  {d x : ℕ} (H : div-ℕ d x) →
  is-nonzero-ℕ x → is-nonzero-ℕ (quotient-div-ℕ d x H)
is-nonzero-quotient-div-ℕ {d} {.(mul-ℕ k d)} (pair k refl) =
  is-nonzero-left-factor-mul-ℕ k d
```
