# Multiplication of matrices

```agda
module linear-algebra.multiplication-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-vectors
open import linear-algebra.matrices-on-rings
open import linear-algebra.vectors
open import linear-algebra.vectors-on-rings

open import ring-theory.rings
```

</details>

## Definition

### Multiplication of matrices

```agda
{-
mul-vector-matrix : {l : Level} → {K : UU l} → {m n : ℕ} →
                     (K → K → K) → (K → K → K) → K →
                     vec K m → Mat K m n → vec K n
mul-vector-matrix _ _ zero empty-vec empty-vec = diagonal zero
mul-vector-matrix mulK addK zero (x ∷ xs) (v ∷ vs) =
  add-vec addK (mul-scalar-vector mulK x v)
               (mul-vector-matrix mulK addK zero xs vs)

mul-Mat : {l' : Level} → {K : UU l'} → {l m n : ℕ} →
          (K → K → K) → (K → K → K) → K →
          Mat K l m → Mat K m n → Mat K l n
mul-Mat _ _ zero empty-vec _ = empty-vec
mul-Mat mulK addK zero (v ∷ vs) m =
  mul-vector-matrix mulK addK zero v m
    ∷ mul-Mat mulK addK zero vs m
-}
```

## Properties

```agda
{-
mul-transpose :
  {l : Level} → {K : UU l} → {m n p : ℕ} →
  {addK : K → K → K} {mulK : K → K → K} {zero : K} →
  ((x y : K) → Id (mulK x y) (mulK y x)) →
  (a : Mat K m n) → (b : Mat K n p) →
  Id (transpose (mul-Mat mulK addK zero a b)) (mul-Mat mulK addK zero (transpose b) (transpose a))
mul-transpose mulK-comm empty-vec b = {!!}
mul-transpose mulK-comm (a ∷ as) b = {!!}
-}
```

## Properties of Matrix Multiplication

 - distributive laws (incomplete)
 - associativity (TODO)
 - identity (TODO)

```agda
{-
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {mulK : K → K → K}
  {zero : K}
  where

  left-distributive-vector-matrix :
    {n m : ℕ} →
    ({l : ℕ} →  Id (diagonal {n = l} zero) (add-vec addK (diagonal zero) (diagonal zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : vec K n) (b : Mat K n m) (c : Mat K n m) →
    Id (mul-vector-matrix mulK addK zero a (add-Mat addK b c))
      (add-vec addK (mul-vector-matrix mulK addK zero a b)
                    (mul-vector-matrix mulK addK zero a c))
  left-distributive-vector-matrix id-vec _ _ _ empty-vec empty-vec empty-vec = id-vec
  left-distributive-vector-matrix id-vec k-distr addK-comm addK-assoc (a ∷ as) (r1 ∷ r1s) (r2 ∷ r2s) =
      ap (λ r → add-vec addK r (mul-vector-matrix mulK addK zero as (add-Mat addK r1s r2s)))
        (left-distributive-scalar-vector {zero = zero} k-distr a r1 r2)
        ∙ (ap (λ r → add-vec addK (add-vec addK (map-vec (mulK a) r1)
                                  (mul-scalar-vector mulK a r2)) r)
              (left-distributive-vector-matrix id-vec k-distr addK-comm addK-assoc as r1s r2s)
          ∙ lemma-shuffle)
    where
    lemma-shuffle : {n : ℕ} →
                    {x y z w : vec K n} →
                    Id (add-vec addK (add-vec addK x y) (add-vec addK z w))
                       (add-vec addK (add-vec addK x z) (add-vec addK y w))
    lemma-shuffle {x = x} {y = y} {z = z} {w = w} =
      associative-add-vectors {zero = zero} addK-assoc (add-vec addK x y) z w
        ∙ (commutative-add-vectors {zero = zero} addK-comm (add-vec addK (add-vec addK x y) z) w
        ∙ (associative-add-vectors {zero = zero} addK-assoc w (add-vec addK x y) z
        ∙ (ap (λ v → add-vec addK (add-vec addK w v) z)
              (commutative-add-vectors {zero = zero} addK-comm x y)
        ∙ (ap (λ v → add-vec addK v z)
              (associative-add-vectors {zero = zero} addK-assoc w y x)
        ∙ (ap (λ v → add-vec addK (add-vec addK v x) z)
              (commutative-add-vectors {zero = zero} addK-comm w y)
        ∙ (inv (associative-add-vectors {zero = zero} addK-assoc (add-vec addK y w) x z)
        ∙ commutative-add-vectors {zero = zero} addK-comm (add-vec addK y w) (add-vec addK x z)))))))

  left-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →  Id (diagonal {n = l} zero) (add-vec addK (diagonal zero) (diagonal zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : Mat K m n) (b : Mat K n p) (c : Mat K n p) →
    Id (mul-Mat mulK addK zero a (add-Mat addK b c))
       (add-Mat addK (mul-Mat mulK addK zero a b)
                     (mul-Mat mulK addK zero a c))
  left-distributive-matrices _ _ _ _ empty-vec _ _ = refl
  left-distributive-matrices id-vec k-distr addK-comm addK-assoc (a ∷ as) b c =
    (ap (λ r → r ∷ mul-Mat mulK addK zero as (add-Mat addK b c))
        (left-distributive-vector-matrix id-vec k-distr addK-comm addK-assoc a b c))
      ∙ ap (_∷_ (add-vec addK (mul-vector-matrix mulK addK zero a b)
                              (mul-vector-matrix mulK addK zero a c)))
          (left-distributive-matrices id-vec k-distr addK-comm addK-assoc as b c)
-}

{- TODO: right distributivity
  right-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →  Id (diagonal {n = l} zero) (add-vec addK (diagonal zero) (diagonal zero))) →
    ((x y z : K) → (Id (mulK (addK x y) z) (addK (mulK x z) (mulK y z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (b : Mat K n p) (c : Mat K n p) (d : Mat K p m) →
    Id (mul-Mat mulK addK zero (add-Mat addK b c) d)
       (add-Mat addK (mul-Mat mulK addK zero b d)
                     (mul-Mat mulK addK zero c d))
  right-distributive-matrices _ _ _ _ empty-vec empty-vec _ = refl
  right-distributive-matrices {p = .zero-ℕ} id-vec k-distr addK-comm addK-assoc (b ∷ bs) (c ∷ cs) empty-vec = {!!}
  right-distributive-matrices id-vec k-distr addK-comm addK-assoc (b ∷ bs) (c ∷ cs) (d ∷ ds) = {!!}
  -- this might also need a proof that zero is the additive identity

  TODO: associativity
  associative-mul-matrices :
  {l : Level} {K : UU l} {n m p q : ℕ} →
  {addK : K → K → K} {mulK : K → K → K} {zero : K} →
  (x : Mat K m n) → (y : Mat K n p) → (z : Mat K p q) →
  Id (mul-Mat mulK addK zero x (mul-Mat mulK addK zero y z))
  (mul-Mat mulK addK zero (mul-Mat mulK addK zero x y) z)
  associative-mul-matrices x y z = {!!}
-}
```
