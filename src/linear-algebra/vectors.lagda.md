# Vectors

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors where

open import foundation
  using (Id ; refl ; ap ; ap-binary ; _∙_ ; inv ; UU ; Level ; lzero)
open import elementary-number-theory.natural-numbers
  using (ℕ ; zero-ℕ ; succ-ℕ)
```
## Idea

An n-vector over some type `K` is a list of n elements from `K`.

## Definition

This definition is the same as the one given in Data.Vec in Agda's standard library.

We also provide some useful functions.

```agda
infixr 5 _∷_

data Vec {l : Level} (K : UU l) : ℕ → UU l where
  empty-Vec : Vec K zero-ℕ
  _∷_ : ∀ {n} → K → Vec K n → Vec K (succ-ℕ n)

repeat : {l : Level} {K : UU l} {n : ℕ} →
         K → Vec K n
repeat {n = zero-ℕ} _ = empty-Vec
repeat {n = succ-ℕ n} x = x ∷ (repeat x)

map : {l : Level} {K K' : UU l} {n : ℕ} →
      (K → K') → Vec K n → Vec K' n
map _ empty-Vec = empty-Vec
map f (x ∷ xs) = f x ∷ map f xs

head : {l : Level} {K : UU l} {n : ℕ} →
       Vec K (succ-ℕ n) → K
head (x ∷ _) = x

tail : {l : Level} {K : UU l} {n : ℕ} →
       Vec K (succ-ℕ n) → Vec K n
tail (_ ∷ xs) = xs
```

## Operations on Vectors

 - scalar-vector multiplication
 - vector-vector addition
 - scalar/dot/inner product

```agda
mul-scalar-vector : {l : Level} → {K : UU l} → {n : ℕ} →
                    (K → K → K) → K → Vec K n → Vec K n
mul-scalar-vector mulK x = map (mulK x)

add-Vec : {l : Level} → {K : UU l} → {n : ℕ} →
          (K → K → K) → Vec K n → Vec K n → Vec K n
add-Vec _ empty-Vec empty-Vec = empty-Vec
add-Vec addK (x ∷ v1) (y ∷ v2) = addK x y ∷ add-Vec addK v1 v2

scalar-product : {l : Level} → {K : UU l} → {n : ℕ} →
                 (K → K → K) → (K → K → K) → K →
                 Vec K n → Vec K n → K
scalar-product _ _ zeroK empty-Vec empty-Vec = zeroK
scalar-product addK mulK zeroK (x ∷ xs) (y ∷ ys) = addK (mulK x y)
  (scalar-product addK mulK zeroK xs ys)
```

## Properties of vector addition

  - left and right units for vector addition
  - vector addition is commutative (if addition in K is)
  - vector addition is associative (if addition in K is)

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {zero : K}
  where
  left-unit-add-vectors :
    {n : ℕ} →
    ((x : K) → Id (addK zero x) x) →
    (v : Vec K n) → Id (add-Vec addK (repeat zero) v) v
  left-unit-add-vectors _ empty-Vec = refl
  left-unit-add-vectors addK-lUnit (x ∷ xs) =
    (ap (λ k → k ∷ add-Vec addK (repeat zero) xs) (addK-lUnit x))
      ∙ ap (λ v → x ∷ v) (left-unit-add-vectors addK-lUnit xs)

  right-unit-add-vectors :
    {n : ℕ} →
    ((x : K) → Id (addK x zero) x) →
    (v : Vec K n) → Id (add-Vec addK v (repeat zero)) v
  right-unit-add-vectors _ empty-Vec = refl
  right-unit-add-vectors addK-rUnit (x ∷ xs) =
    (ap (λ k → k ∷ add-Vec addK xs (repeat zero)) (addK-rUnit x))
      ∙ ap (λ v → x ∷ v) (right-unit-add-vectors addK-rUnit xs)

  commutative-add-vectors :
    {n : ℕ} →
    ((x y : K) → Id (addK x y) (addK y x)) →
    (a b : Vec K n) → Id (add-Vec addK a b) (add-Vec addK b a)
  commutative-add-vectors _ empty-Vec empty-Vec = refl
  commutative-add-vectors addK-comm (x ∷ a) (y ∷ b) =
    ap (λ k → k ∷ add-Vec addK a b) (addK-comm x y)
    ∙ ap (_∷_ (addK y x)) (commutative-add-vectors addK-comm a b)

  associative-add-vectors :
    {n : ℕ} →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a b c : Vec K n) →
    Id (add-Vec addK a (add-Vec addK b c)) (add-Vec addK (add-Vec addK a b) c)
  associative-add-vectors _ empty-Vec empty-Vec empty-Vec = refl
  associative-add-vectors addK-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    ap (λ k → k ∷ (add-Vec addK xs (add-Vec addK ys zs))) (addK-assoc x y z)
      ∙ ap (_∷_ (addK (addK x y) z)) (associative-add-vectors addK-assoc xs ys zs)
```

## Properties of scalar-vector multiplication
  - left distributive k(v1 + v2) = kv1 + kv2

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {mulK : K → K → K}
  {zero : K}
  where
  left-distributive-scalar-vector :
    {n : ℕ} →
    ((x y z : K) → Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z))) →
    (k : K) → (v1 v2 : Vec K n) →
    Id (mul-scalar-vector mulK k (add-Vec addK v1 v2))
       (add-Vec addK (mul-scalar-vector mulK k v1) (mul-scalar-vector mulK k v2))
  left-distributive-scalar-vector _ _ empty-Vec empty-Vec = refl
  left-distributive-scalar-vector k-distr k (x ∷ xs) (y ∷ ys) =
    (ap (λ k' → k' ∷ mul-scalar-vector mulK k (add-Vec addK xs ys)) (k-distr k x y))
      ∙ ap (_∷_ (addK (mulK k x) (mulK k y)))
           (left-distributive-scalar-vector k-distr k xs ys)
```
