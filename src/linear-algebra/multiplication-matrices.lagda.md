# Multiplication of matrices

```agda
module linear-algebra.multiplication-matrices where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Definition

### Multiplication of matrices

```agda
{-
mul-tuple-matrix : {l : Level} → {K : UU l} → {m n : ℕ} →
                     (K → K → K) → (K → K → K) → K →
                     tuple K m → Mat K m n → tuple K n
mul-tuple-matrix _ _ zero empty-tuple empty-tuple = diagonal-product zero
mul-tuple-matrix mulK addK zero (x ∷ xs) (v ∷ vs) =
  add-tuple addK (mul-scalar-tuple mulK x v)
               (mul-tuple-matrix mulK addK zero xs vs)

mul-Mat : {l' : Level} → {K : UU l'} → {l m n : ℕ} →
          (K → K → K) → (K → K → K) → K →
          Mat K l m → Mat K m n → Mat K l n
mul-Mat _ _ zero empty-tuple _ = empty-tuple
mul-Mat mulK addK zero (v ∷ vs) m =
  mul-tuple-matrix mulK addK zero v m
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
  Id
    (transpose (mul-Mat mulK addK zero a b))
    (mul-Mat mulK addK zero (transpose b) (transpose a))
mul-transpose mulK-comm empty-tuple b = {!!}
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

  left-distributive-tuple-matrix :
    {n m : ℕ} →
    ({l : ℕ} →  Id (diagonal-product {n = l} zero)
    (add-tuple addK (diagonal-product zero) (diagonal-product zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : tuple K n) (b : Mat K n m) (c : Mat K n m) →
    Id (mul-tuple-matrix mulK addK zero a (add-Mat addK b c))
      (add-tuple addK (mul-tuple-matrix mulK addK zero a b)
                    (mul-tuple-matrix mulK addK zero a c))
  left-distributive-tuple-matrix id-tuple _ _ _ empty-tuple empty-tuple empty-tuple =
    id-tuple
  left-distributive-tuple-matrix
    id-tuple k-distr addK-comm addK-associative (a ∷ as) (r1 ∷ r1s) (r2 ∷ r2s) =
      ap
        ( λ r →
          add-tuple addK r
            (mul-tuple-matrix mulK addK zero as (add-Mat addK r1s r2s)))
        (left-distributive-scalar-tuple {zero = zero} k-distr a r1 r2)
        ∙ (ap (λ r → add-tuple addK (add-tuple addK (map-tuple (mulK a) r1)
                                  (mul-scalar-tuple mulK a r2)) r)
              (left-distributive-tuple-matrix
                id-tuple k-distr addK-comm addK-associative as r1s r2s)
          ∙ lemma-shuffle)
    where
    lemma-shuffle : {n : ℕ} →
                    {x y z w : tuple K n} →
                    Id (add-tuple addK (add-tuple addK x y) (add-tuple addK z w))
                       (add-tuple addK (add-tuple addK x z) (add-tuple addK y w))
    lemma-shuffle {x = x} {y = y} {z = z} {w = w} =
      associative-add-tuples {zero = zero} addK-associative (add-tuple addK x y) z w
        ∙ (commutative-add-tuples
            {zero = zero} addK-comm (add-tuple addK (add-tuple addK x y) z) w
        ∙ (associative-add-tuples
            {zero = zero} addK-associative w (add-tuple addK x y) z
        ∙ (ap (λ v → add-tuple addK (add-tuple addK w v) z)
              (commutative-add-tuples {zero = zero} addK-comm x y)
        ∙ (ap (λ v → add-tuple addK v z)
              (associative-add-tuples {zero = zero} addK-associative w y x)
        ∙ (ap (λ v → add-tuple addK (add-tuple addK v x) z)
              (commutative-add-tuples {zero = zero} addK-comm w y)
        ∙ (inv (associative-add-tuples
            {zero = zero} addK-associative (add-tuple addK y w) x z)
        ∙ commutative-add-tuples
            {zero = zero} addK-comm (add-tuple addK y w) (add-tuple addK x z)))))))

  left-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →
      Id
        (diagonal-product {n = l} zero)
        (add-tuple addK (diagonal-product zero) (diagonal-product zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : Mat K m n) (b : Mat K n p) (c : Mat K n p) →
    Id (mul-Mat mulK addK zero a (add-Mat addK b c))
       (add-Mat addK (mul-Mat mulK addK zero a b)
                     (mul-Mat mulK addK zero a c))
  left-distributive-matrices _ _ _ _ empty-tuple _ _ = refl
  left-distributive-matrices id-tuple k-distr addK-comm addK-associative (a ∷ as) b c =
    (ap (λ r → r ∷ mul-Mat mulK addK zero as (add-Mat addK b c))
        (left-distributive-tuple-matrix
          id-tuple k-distr addK-comm addK-associative a b c))
      ∙ ap (_∷_ (add-tuple addK (mul-tuple-matrix mulK addK zero a b)
                              (mul-tuple-matrix mulK addK zero a c)))
          (left-distributive-matrices
            id-tuple k-distr addK-comm addK-associative as b c)
-}

{- TODO: right distributivity
  right-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →
      Id
        (diagonal-product {n = l} zero)
        (add-tuple addK (diagonal-product zero) (diagonal-product zero))) →
    ((x y z : K) → (Id (mulK (addK x y) z) (addK (mulK x z) (mulK y z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (b : Mat K n p) (c : Mat K n p) (d : Mat K p m) →
    Id (mul-Mat mulK addK zero (add-Mat addK b c) d)
       (add-Mat addK (mul-Mat mulK addK zero b d)
                     (mul-Mat mulK addK zero c d))
  right-distributive-matrices _ _ _ _ empty-tuple empty-tuple _ = refl
  right-distributive-matrices
    {p = .zero-ℕ}
    id-tuple k-distr addK-comm addK-associative (b ∷ bs) (c ∷ cs) empty-tuple =
    {!!}
  right-distributive-matrices
    id-tuple k-distr addK-comm addK-associative (b ∷ bs) (c ∷ cs) (d ∷ ds) =
    {!!}
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
