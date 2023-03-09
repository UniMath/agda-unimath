# Multiplication of integers

```agda
module elementary-number-theory.multiplication-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

## Definitions

### The standard definition of multiplication on ℤ

```agda
mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inl zero-ℕ) l = neg-ℤ l
mul-ℤ (inl (succ-ℕ x)) l = add-ℤ (neg-ℤ l) (mul-ℤ (inl x) l)
mul-ℤ (inr (inl star)) l = zero-ℤ
mul-ℤ (inr (inr zero-ℕ)) l = l
mul-ℤ (inr (inr (succ-ℕ x))) l = add-ℤ l (mul-ℤ (inr (inr x)) l)

mul-ℤ' : ℤ → ℤ → ℤ
mul-ℤ' x y = mul-ℤ y x

ap-mul-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → mul-ℤ x y ＝ mul-ℤ x' y'
ap-mul-ℤ p q = ap-binary mul-ℤ p q
```

### A definition of multiplication that connects with multiplication on ℕ

```agda
explicit-mul-ℤ : ℤ → ℤ → ℤ
explicit-mul-ℤ (inl x) (inl y) = int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))
explicit-mul-ℤ (inl x) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inl x) (inr (inr y)) =
  neg-ℤ (int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inl y) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inl y) =
  neg-ℤ (int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inl star)) (inr (inr y)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inr y)) = int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))

explicit-mul-ℤ' : ℤ → ℤ → ℤ
explicit-mul-ℤ' x y = explicit-mul-ℤ y x
```

### A definition of being equal up to sign

```agda
is-plus-or-minus-ℤ : ℤ → ℤ → UU lzero
is-plus-or-minus-ℤ x y = (x ＝ y) + (mul-ℤ neg-one-ℤ x ＝ y)
```

## Properties

### Laws for multiplication on ℤ

```agda
left-zero-law-mul-ℤ : (k : ℤ) → mul-ℤ zero-ℤ k ＝ zero-ℤ
left-zero-law-mul-ℤ k = refl

right-zero-law-mul-ℤ : (k : ℤ) → mul-ℤ k zero-ℤ ＝ zero-ℤ
right-zero-law-mul-ℤ (inl zero-ℕ) = refl
right-zero-law-mul-ℤ (inl (succ-ℕ n)) =
  right-zero-law-mul-ℤ (inl n)
right-zero-law-mul-ℤ (inr (inl star)) = refl
right-zero-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-zero-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  right-zero-law-mul-ℤ (inr (inr n))

left-unit-law-mul-ℤ : (k : ℤ) → mul-ℤ one-ℤ k ＝ k
left-unit-law-mul-ℤ k = refl

right-unit-law-mul-ℤ : (k : ℤ) → mul-ℤ k one-ℤ ＝ k
right-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap (add-ℤ (neg-one-ℤ)) (right-unit-law-mul-ℤ (inl n))
right-unit-law-mul-ℤ (inr (inl star)) = refl
right-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (add-ℤ one-ℤ) (right-unit-law-mul-ℤ (inr (inr n)))

left-neg-unit-law-mul-ℤ : (k : ℤ) → mul-ℤ neg-one-ℤ k ＝ neg-ℤ k
left-neg-unit-law-mul-ℤ k = refl

right-neg-unit-law-mul-ℤ : (k : ℤ) → mul-ℤ k neg-one-ℤ ＝ neg-ℤ k
right-neg-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-neg-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap (add-ℤ one-ℤ) (right-neg-unit-law-mul-ℤ (inl n))
right-neg-unit-law-mul-ℤ (inr (inl star)) = refl
right-neg-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-neg-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (add-ℤ neg-one-ℤ) (right-neg-unit-law-mul-ℤ (inr (inr n)))

left-successor-law-mul-ℤ :
  (k l : ℤ) → mul-ℤ (succ-ℤ k) l ＝ add-ℤ l (mul-ℤ k l)
left-successor-law-mul-ℤ (inl zero-ℕ) l =
  inv (right-inverse-law-add-ℤ l)
left-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ( inv (left-unit-law-add-ℤ (mul-ℤ (inl n) l))) ∙
    ( ap
      ( add-ℤ' (mul-ℤ (inl n) l))
      ( inv (right-inverse-law-add-ℤ l)))) ∙
  ( associative-add-ℤ l (neg-ℤ l) (mul-ℤ (inl n) l))
left-successor-law-mul-ℤ (inr (inl star)) l =
  inv (right-unit-law-add-ℤ l)
left-successor-law-mul-ℤ (inr (inr n)) l = refl

left-predecessor-law-mul-ℤ :
  (k l : ℤ) → mul-ℤ (pred-ℤ k) l ＝ add-ℤ (neg-ℤ l) (mul-ℤ k l)
left-predecessor-law-mul-ℤ (inl n) l = refl
left-predecessor-law-mul-ℤ (inr (inl star)) l =
  ( left-neg-unit-law-mul-ℤ l) ∙
  ( inv (right-unit-law-add-ℤ (neg-ℤ l)))
left-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l =
  inv (left-inverse-law-add-ℤ l)
left-predecessor-law-mul-ℤ (inr (inr (succ-ℕ x))) l =
   ( ap
     ( add-ℤ' (mul-ℤ (in-pos x) l))
     ( inv (left-inverse-law-add-ℤ l))) ∙
   ( associative-add-ℤ (neg-ℤ l) l (mul-ℤ (in-pos x) l))

right-successor-law-mul-ℤ :
  (k l : ℤ) → mul-ℤ k (succ-ℤ l) ＝ add-ℤ k (mul-ℤ k l)
right-successor-law-mul-ℤ (inl zero-ℕ) l = inv (pred-neg-ℤ l)
right-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (succ-ℤ l)) ∙
  ( ( ap (add-ℤ (neg-ℤ (succ-ℤ l))) (right-successor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv (associative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl n) (mul-ℤ (inl n) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (inl n) l))
          { x = add-ℤ (neg-ℤ (succ-ℤ l)) (inl n)}
          { y = add-ℤ (inl (succ-ℕ n)) (neg-ℤ l)}
          ( ( right-successor-law-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n))) ∙
            ( ( ap succ-ℤ
                ( commutative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n)))) ∙
              ( ( inv
                  ( right-successor-law-add-ℤ
                    ( inl (succ-ℕ n))
                    ( neg-ℤ (succ-ℤ l)))) ∙
                ( ap
                  ( add-ℤ (inl (succ-ℕ n)))
                  ( ( ap succ-ℤ (inv (pred-neg-ℤ l))) ∙
                    ( issec-pred-ℤ (neg-ℤ l)))))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) (neg-ℤ l) (mul-ℤ (inl n) l)))))
right-successor-law-mul-ℤ (inr (inl star)) l = refl
right-successor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-successor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos n) (succ-ℤ l)) ∙
  ( ( ap (add-ℤ (succ-ℤ l)) (right-successor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (succ-ℤ l) (in-pos n) (mul-ℤ (in-pos n) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (in-pos n) l))
          { x = add-ℤ (succ-ℤ l) (in-pos n)}
          { y = add-ℤ (in-pos (succ-ℕ n)) l}
          ( ( left-successor-law-add-ℤ l (in-pos n)) ∙
            ( ( ap succ-ℤ (commutative-add-ℤ l (in-pos n))) ∙
              ( inv (left-successor-law-add-ℤ (in-pos n) l))))) ∙
        ( associative-add-ℤ (inr (inr (succ-ℕ n))) l (mul-ℤ (inr (inr n)) l)))))

right-predecessor-law-mul-ℤ :
  (k l : ℤ) → mul-ℤ k (pred-ℤ l) ＝ add-ℤ (neg-ℤ k) (mul-ℤ k l)
right-predecessor-law-mul-ℤ (inl zero-ℕ) l =
  ( left-neg-unit-law-mul-ℤ (pred-ℤ l)) ∙
  ( neg-pred-ℤ l)
right-predecessor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (pred-ℤ l)) ∙
  ( ( ap (add-ℤ (neg-ℤ (pred-ℤ l))) (right-predecessor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv
        ( associative-add-ℤ (neg-ℤ (pred-ℤ l)) (in-pos n) (mul-ℤ (inl n) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (inl n) l))
          { x = add-ℤ (neg-ℤ (pred-ℤ l)) (inr (inr n))}
          { y = add-ℤ (neg-ℤ (inl (succ-ℕ n))) (neg-ℤ l)}
          ( ( ap (add-ℤ' (in-pos n)) (neg-pred-ℤ l)) ∙
            ( ( left-successor-law-add-ℤ (neg-ℤ l) (in-pos n)) ∙
              ( ( ap succ-ℤ (commutative-add-ℤ (neg-ℤ l) (in-pos n))) ∙
                ( inv (left-successor-law-add-ℤ (in-pos n) (neg-ℤ l))))))) ∙
        ( associative-add-ℤ (in-pos (succ-ℕ n)) (neg-ℤ l) (mul-ℤ (inl n) l)))))
right-predecessor-law-mul-ℤ (inr (inl star)) l = refl
right-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-predecessor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos n) (pred-ℤ l)) ∙
  ( ( ap (add-ℤ (pred-ℤ l)) (right-predecessor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (pred-ℤ l) (inl n) (mul-ℤ (inr (inr n)) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (in-pos n) l))
          { x = add-ℤ (pred-ℤ l) (inl n)}
          { y = add-ℤ (neg-ℤ (in-pos (succ-ℕ n))) l}
          ( ( left-predecessor-law-add-ℤ l (inl n)) ∙
            ( ( ap pred-ℤ (commutative-add-ℤ l (inl n))) ∙
              ( inv (left-predecessor-law-add-ℤ (inl n) l))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) l (mul-ℤ (inr (inr n)) l)))))

right-distributive-mul-add-ℤ :
  (k l m : ℤ) → mul-ℤ (add-ℤ k l) m ＝ add-ℤ (mul-ℤ k m) (mul-ℤ l m)
right-distributive-mul-add-ℤ (inl zero-ℕ) l m =
  ( left-predecessor-law-mul-ℤ l m) ∙
  ( ap
    ( add-ℤ' (mul-ℤ l m))
    ( inv
      ( ( left-predecessor-law-mul-ℤ zero-ℤ m) ∙
        ( right-unit-law-add-ℤ (neg-ℤ m)))))
right-distributive-mul-add-ℤ (inl (succ-ℕ x)) l m =
  ( left-predecessor-law-mul-ℤ (add-ℤ (inl x) l) m) ∙
  ( ( ap (add-ℤ (neg-ℤ m)) (right-distributive-mul-add-ℤ (inl x) l m)) ∙
    ( inv (associative-add-ℤ (neg-ℤ m) (mul-ℤ (inl x) m) (mul-ℤ l m))))
right-distributive-mul-add-ℤ (inr (inl star)) l m = refl
right-distributive-mul-add-ℤ (inr (inr zero-ℕ)) l m =
  left-successor-law-mul-ℤ l m
right-distributive-mul-add-ℤ (inr (inr (succ-ℕ n))) l m =
  ( left-successor-law-mul-ℤ (add-ℤ (in-pos n) l) m) ∙
  ( ( ap (add-ℤ m) (right-distributive-mul-add-ℤ (inr (inr n)) l m)) ∙
    ( inv (associative-add-ℤ m (mul-ℤ (in-pos n) m) (mul-ℤ l m))))

left-negative-law-mul-ℤ :
  (k l : ℤ) → mul-ℤ (neg-ℤ k) l ＝ neg-ℤ (mul-ℤ k l)
left-negative-law-mul-ℤ (inl zero-ℕ) l =
  ( left-unit-law-mul-ℤ l) ∙
  ( inv (neg-neg-ℤ l))
left-negative-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap (mul-ℤ' l) (neg-pred-ℤ (inl n))) ∙
  ( ( left-successor-law-mul-ℤ (neg-ℤ (inl n)) l) ∙
    ( ( ap (add-ℤ l) (left-negative-law-mul-ℤ (inl n) l)) ∙
      ( right-negative-law-add-ℤ l (mul-ℤ (inl n) l))))
left-negative-law-mul-ℤ (inr (inl star)) l = refl
left-negative-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
left-negative-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-predecessor-law-mul-ℤ (inl n) l) ∙
  ( ( ap (add-ℤ (neg-ℤ l)) (left-negative-law-mul-ℤ (inr (inr n)) l)) ∙
    ( inv (distributive-neg-add-ℤ l (mul-ℤ (in-pos n) l))))

associative-mul-ℤ :
  (k l m : ℤ) → mul-ℤ (mul-ℤ k l) m ＝ mul-ℤ k (mul-ℤ l m)
associative-mul-ℤ (inl zero-ℕ) l m =
  left-negative-law-mul-ℤ l m
associative-mul-ℤ (inl (succ-ℕ n)) l m =
  ( right-distributive-mul-add-ℤ (neg-ℤ l) (mul-ℤ (inl n) l) m) ∙
  ( ( ap (add-ℤ (mul-ℤ (neg-ℤ l) m)) (associative-mul-ℤ (inl n) l m)) ∙
    ( ap
      ( add-ℤ' (mul-ℤ (inl n) (mul-ℤ l m)))
      ( left-negative-law-mul-ℤ l m)))
associative-mul-ℤ (inr (inl star)) l m = refl
associative-mul-ℤ (inr (inr zero-ℕ)) l m = refl
associative-mul-ℤ (inr (inr (succ-ℕ n))) l m =
  ( right-distributive-mul-add-ℤ l (mul-ℤ (in-pos n) l) m) ∙
  ( ap (add-ℤ (mul-ℤ l m)) (associative-mul-ℤ (inr (inr n)) l m))

commutative-mul-ℤ :
  (k l : ℤ) → mul-ℤ k l ＝ mul-ℤ l k
commutative-mul-ℤ (inl zero-ℕ) l = inv (right-neg-unit-law-mul-ℤ l)
commutative-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap (add-ℤ (neg-ℤ l)) (commutative-mul-ℤ (inl n) l)) ∙
  ( inv (right-predecessor-law-mul-ℤ l (inl n)))
commutative-mul-ℤ (inr (inl star)) l = inv (right-zero-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr zero-ℕ)) l = inv (right-unit-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( ap (add-ℤ l) (commutative-mul-ℤ (inr (inr n)) l)) ∙
  ( inv (right-successor-law-mul-ℤ l (in-pos n)))

left-distributive-mul-add-ℤ :
  (m k l : ℤ) → mul-ℤ m (add-ℤ k l) ＝ add-ℤ (mul-ℤ m k) (mul-ℤ m l)
left-distributive-mul-add-ℤ m k l =
  commutative-mul-ℤ m (add-ℤ k l) ∙
    ( ( right-distributive-mul-add-ℤ k l m) ∙
      ( ap-add-ℤ (commutative-mul-ℤ k m) (commutative-mul-ℤ l m)))

right-negative-law-mul-ℤ :
  (k l : ℤ) → mul-ℤ k (neg-ℤ l) ＝ neg-ℤ (mul-ℤ k l)
right-negative-law-mul-ℤ k l =
  ( ( commutative-mul-ℤ k (neg-ℤ l)) ∙
    ( left-negative-law-mul-ℤ l k)) ∙
  ( ap neg-ℤ (commutative-mul-ℤ l k))

interchange-law-mul-mul-ℤ : interchange-law mul-ℤ mul-ℤ
interchange-law-mul-mul-ℤ =
  interchange-law-commutative-and-associative
    mul-ℤ
    commutative-mul-ℤ
    associative-mul-ℤ

is-mul-neg-one-neg-ℤ : (x : ℤ) → neg-ℤ x ＝ mul-ℤ neg-one-ℤ x
is-mul-neg-one-neg-ℤ x = refl

is-mul-neg-one-neg-ℤ' : (x : ℤ) → neg-ℤ x ＝ mul-ℤ x neg-one-ℤ
is-mul-neg-one-neg-ℤ' x =
  is-mul-neg-one-neg-ℤ x ∙ commutative-mul-ℤ neg-one-ℤ x

double-negative-law-mul-ℤ : (k l : ℤ) → mul-ℤ (neg-ℤ k) (neg-ℤ l) ＝ mul-ℤ k l
double-negative-law-mul-ℤ k l = equational-reasoning
  mul-ℤ (neg-ℤ k) (neg-ℤ l)
  ＝ neg-ℤ (mul-ℤ k (neg-ℤ l))
    by left-negative-law-mul-ℤ k (neg-ℤ l)
  ＝ neg-ℤ (neg-ℤ (mul-ℤ k l))
    by ap neg-ℤ (right-negative-law-mul-ℤ k l)
  ＝ mul-ℤ k l
    by neg-neg-ℤ (mul-ℤ k l)
```

### Positivity of multiplication

```agda
is-positive-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (mul-ℤ x y)
is-positive-mul-ℤ {inr (inr zero-ℕ)} {inr (inr y)} H K = star
is-positive-mul-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K =
  is-positive-add-ℤ {inr (inr y)} K
    ( is-positive-mul-ℤ {inr (inr x)} {inr (inr y)} H K)
```

### Computing multiplication of integers that come from natural numbers

```agda
mul-int-ℕ : (x y : ℕ) → mul-ℤ (int-ℕ x) (int-ℕ y) ＝ int-ℕ (mul-ℕ x y)
mul-int-ℕ zero-ℕ y = refl
mul-int-ℕ (succ-ℕ x) y =
  ( ap (mul-ℤ' (int-ℕ y)) (inv (succ-int-ℕ x))) ∙
  ( ( left-successor-law-mul-ℤ (int-ℕ x) (int-ℕ y)) ∙
    ( ( ( ap (add-ℤ (int-ℕ y)) (mul-int-ℕ x y)) ∙
        ( add-int-ℕ y (mul-ℕ x y))) ∙
      ( ap int-ℕ (commutative-add-ℕ y (mul-ℕ x y)))))

compute-mul-ℤ : (x y : ℤ) → mul-ℤ x y ＝ explicit-mul-ℤ x y
compute-mul-ℤ (inl zero-ℕ) (inl y) =
  inv (ap int-ℕ (left-unit-law-mul-ℕ (succ-ℕ y)))
compute-mul-ℤ (inl (succ-ℕ x)) (inl y) =
  ( ( ap (add-ℤ (int-ℕ (succ-ℕ y))) (compute-mul-ℤ (inl x) (inl y))) ∙
    ( commutative-add-ℤ
      ( int-ℕ (succ-ℕ y))
      ( int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))))) ∙
  ( add-int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)) (succ-ℕ y))
compute-mul-ℤ (inl zero-ℕ) (inr (inl star)) = refl
compute-mul-ℤ (inl zero-ℕ) (inr (inr x)) = ap inl (inv (left-unit-law-add-ℕ x))
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inl star)) = right-zero-law-mul-ℤ (inl x)
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inr y)) =
  ( ( ( ap (add-ℤ (inl y)) (compute-mul-ℤ (inl x) (inr (inr y)))) ∙
      ( inv
        ( distributive-neg-add-ℤ
          ( inr (inr y))
          ( int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))) ∙
    ( ap
      ( neg-ℤ)
      ( commutative-add-ℤ
        ( int-ℕ (succ-ℕ y))
        ( int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))) ∙
  ( ap neg-ℤ (add-int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)) (succ-ℕ y)))
compute-mul-ℤ (inr (inl star)) (inl y) = refl
compute-mul-ℤ (inr (inr zero-ℕ)) (inl y) = ap inl (inv (left-unit-law-add-ℕ y))
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inl y) =
  ( ap (add-ℤ (inl y)) (compute-mul-ℤ (inr (inr x)) (inl y))) ∙
  ( ( ( inv
        ( distributive-neg-add-ℤ
          ( inr (inr y))
          ( inr (inr (add-ℕ (mul-ℕ x (succ-ℕ y)) y))))) ∙
      ( ap
        ( neg-ℤ)
        ( ( add-int-ℕ (succ-ℕ y) (mul-ℕ (succ-ℕ x) (succ-ℕ y))) ∙
          ( ap
            ( inr ∘ inr)
            ( left-successor-law-add-ℕ y (add-ℕ (mul-ℕ x (succ-ℕ y)) y)))))) ∙
    ( ap inl (commutative-add-ℕ y (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))
compute-mul-ℤ (inr (inl star)) (inr (inl star)) = refl
compute-mul-ℤ (inr (inl star)) (inr (inr y)) = refl
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inl star)) = refl
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inl star)) =
  right-zero-law-mul-ℤ (inr (inr (succ-ℕ x)))
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inr y)) =
  ap ( inr ∘ inr)
     ( inv
       ( ( ap (add-ℕ' y) (left-zero-law-mul-ℕ (succ-ℕ y))) ∙
         ( left-unit-law-add-ℕ y)))
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inr y)) =
  ( ap (add-ℤ (inr (inr y))) (compute-mul-ℤ (inr (inr x)) (inr (inr y)))) ∙
  ( ( add-int-ℕ (succ-ℕ y) (mul-ℕ (succ-ℕ x) (succ-ℕ y))) ∙
    ( ap int-ℕ (commutative-add-ℕ (succ-ℕ y) (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))
```

### Linearity of the difference

```agda
linear-diff-ℤ :
  (z x y : ℤ) → diff-ℤ (mul-ℤ z x) (mul-ℤ z y) ＝ mul-ℤ z (diff-ℤ x y)
linear-diff-ℤ z x y =
  ( ap (add-ℤ (mul-ℤ z x)) (inv (right-negative-law-mul-ℤ z y))) ∙
  ( inv (left-distributive-mul-add-ℤ z x (neg-ℤ y)))

linear-diff-ℤ' :
  (x y z : ℤ) → diff-ℤ (mul-ℤ x z) (mul-ℤ y z) ＝ mul-ℤ (diff-ℤ x y) z
linear-diff-ℤ' x y z =
  ( ap (add-ℤ (mul-ℤ x z)) (inv (left-negative-law-mul-ℤ y z))) ∙
  ( inv (right-distributive-mul-add-ℤ x (neg-ℤ y) z))
```

```agda
is-zero-is-zero-mul-ℤ :
  (x y : ℤ) → is-zero-ℤ (mul-ℤ x y) → (is-zero-ℤ x) + (is-zero-ℤ y)
is-zero-is-zero-mul-ℤ (inl x) (inl y) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl x) (inl y)) ∙ H))
is-zero-is-zero-mul-ℤ (inl x) (inr (inl star)) H = inr refl
is-zero-is-zero-mul-ℤ (inl x) (inr (inr y)) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl x) (inr (inr y))) ∙ H))
is-zero-is-zero-mul-ℤ (inr (inl star)) y H = inl refl
is-zero-is-zero-mul-ℤ (inr (inr x)) (inl y) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inl y)) ∙ H))
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inl star)) H = inr refl
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inr y)) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inr (inr y))) ∙ H))
```

### Injectivity of multiplication

```agda
is-injective-mul-ℤ :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (mul-ℤ x)
is-injective-mul-ℤ x f {y} {z} p =
  eq-diff-ℤ
    ( map-left-unit-law-coprod-is-empty
      ( is-zero-ℤ x)
      ( is-zero-ℤ (diff-ℤ y z))
      ( f)
      ( is-zero-is-zero-mul-ℤ x
        ( diff-ℤ y z)
        ( inv (linear-diff-ℤ x y z) ∙ is-zero-diff-ℤ p)))

is-injective-mul-ℤ' :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (mul-ℤ' x)
is-injective-mul-ℤ' x f {y} {z} p =
  is-injective-mul-ℤ x f (commutative-mul-ℤ x y ∙ (p ∙ commutative-mul-ℤ z x))
```

### Multiplication by a nonzero integer is an embedding

```agda
is-emb-mul-ℤ : (x : ℤ) → is-nonzero-ℤ x → is-emb (mul-ℤ x)
is-emb-mul-ℤ x f = is-emb-is-injective is-set-ℤ (is-injective-mul-ℤ x f)

is-emb-mul-ℤ' : (x : ℤ) → is-nonzero-ℤ x → is-emb (mul-ℤ' x)
is-emb-mul-ℤ' x f = is-emb-is-injective is-set-ℤ (is-injective-mul-ℤ' x f)
```

```agda
is-positive-left-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (mul-ℤ x y) → is-positive-ℤ y → is-positive-ℤ x
is-positive-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inl star)} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ zero-ℤ (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inr x)} {inr (inr y)} H K = star

is-positive-right-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (mul-ℤ x y) → is-positive-ℤ x → is-positive-ℤ y
is-positive-right-factor-mul-ℤ {x} {y} H =
  is-positive-left-factor-mul-ℤ (is-positive-eq-ℤ (commutative-mul-ℤ x y) H)

-- Lemmas about nonnegative integers

is-nonnegative-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ y →
  is-nonnegative-ℤ (mul-ℤ x y)
is-nonnegative-mul-ℤ {inr (inl star)} {y} H K = star
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inl star)} H K =
  is-nonnegative-eq-ℤ (inv (right-zero-law-mul-ℤ (inr (inr x)))) star
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inr y)} H K =
  is-nonnegative-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inr (inr y)))) star

is-nonnegative-left-factor-mul-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ (mul-ℤ x y) → is-positive-ℤ y → is-nonnegative-ℤ x
is-nonnegative-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  ex-falso (is-nonnegative-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H)
is-nonnegative-left-factor-mul-ℤ {inr x} {inr y} H K = star

is-nonnegative-right-factor-mul-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ (mul-ℤ x y) → is-positive-ℤ x → is-nonnegative-ℤ y
is-nonnegative-right-factor-mul-ℤ {x} {y} H =
  is-nonnegative-left-factor-mul-ℤ
    ( is-nonnegative-eq-ℤ (commutative-mul-ℤ x y) H)
```

```agda
preserves-leq-mul-ℤ :
  (x y z : ℤ) → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (mul-ℤ z x) (mul-ℤ z y)
preserves-leq-mul-ℤ x y (inr (inl star)) star K = star
preserves-leq-mul-ℤ x y (inr (inr zero-ℕ)) star K = K
preserves-leq-mul-ℤ x y (inr (inr (succ-ℕ n))) star K =
  preserves-leq-add-ℤ {x} {y}
    { mul-ℤ (inr (inr n)) x}
    { mul-ℤ (inr (inr n)) y}
    ( K)
    ( preserves-leq-mul-ℤ x y (inr (inr n)) star K)

preserves-leq-mul-ℤ' :
  (x y z : ℤ) → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (mul-ℤ x z) (mul-ℤ y z)
preserves-leq-mul-ℤ' x y z H K =
  concatenate-eq-leq-eq-ℤ
    ( commutative-mul-ℤ x z)
    ( preserves-leq-mul-ℤ x y z H K)
    ( commutative-mul-ℤ z y)
```
