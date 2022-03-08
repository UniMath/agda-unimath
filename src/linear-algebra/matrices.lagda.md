# Matrices
```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.matrices where

open import foundation
  using (Id ; refl ; ap ; ap-binary ; _∙_ ; inv ; UU ; Level ; lzero)
open import elementary-number-theory.natural-numbers
  using (ℕ ; zero-ℕ ; succ-ℕ)

open import linear-algebra.vectors

```

##  Definition

`Mat K m n` is the type of m × n matrices with elements from `K`, as a vector of vectors.

The definition is based on exercises from [Computer Aided Formal Reasoning](http://www.cs.nott.ac.uk/~psztxa/g53cfr/)

Alternatively, an m × n could be seen as map from `(Fin m × Fin n)` to `K`

```agda
Mat : {l : Level} → (K : UU l) → ℕ → ℕ → UU l
Mat K m n = Vec (Vec K n) m
```

## Operations on matrices

We take the binary operations in K as arguments.

For vector-matrix and matrix-matrix multiplication we also need a zero element, assumed to be the additive identity in K.

```agda
add-Mat : {l : Level} → {K : UU l} → {m n : ℕ} →
          (K → K → K) → Mat K m n → Mat K m n → Mat K m n
add-Mat _ empty-Vec empty-Vec = empty-Vec
add-Mat addK (v1 ∷ v1s) (v2 ∷ v2s) = add-Vec addK v1 v2 ∷ add-Mat addK v1s v2s

mul-scalar-matrix : {l : Level} → {K : UU l} → {m n : ℕ} →
                     (K → K → K) → K → Mat K m n → Mat K m n
mul-scalar-matrix _ x empty-Vec = empty-Vec
mul-scalar-matrix mulK x (v ∷ vs) = mul-scalar-vector mulK x v
                                    ∷ mul-scalar-matrix mulK x vs

mul-vector-matrix : {l : Level} → {K : UU l} → {m n : ℕ} →
                     (K → K → K) → (K → K → K) → K →
                     Vec K m → Mat K m n → Vec K n
mul-vector-matrix _ _ zero empty-Vec empty-Vec = repeat zero
mul-vector-matrix mulK addK zero (x ∷ xs) (v ∷ vs) =
  add-Vec addK (mul-scalar-vector mulK x v)
               (mul-vector-matrix mulK addK zero xs vs)

mul-Mat : {l' : Level} → {K : UU l'} → {l m n : ℕ} →
          (K → K → K) → (K → K → K) → K →
          Mat K l m → Mat K m n → Mat K l n
mul-Mat _ _ zero empty-Vec _ = empty-Vec
mul-Mat mulK addK zero (v ∷ vs) m =
  mul-vector-matrix mulK addK zero v m
    ∷ mul-Mat mulK addK zero vs m

transpose : {l : Level} → {K : UU l} → {m n : ℕ} →
            Mat K m n → Mat K n m
transpose {n = zero-ℕ} x = empty-Vec
transpose {n = succ-ℕ n} x = map head x ∷ transpose (map tail x)
```

## Properties of Matrix Addition

 - has identity (if K does)
 - commutative (if addK is)
 - associative (if mulK is)

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {zero : K}
  where
  left-unit-add-matrices :
    {n m : ℕ} →
    ((x : K) → Id (addK zero x) x) →
    (v : Mat K m n) → Id (add-Mat addK (repeat (repeat zero)) v) v
  left-unit-add-matrices _ empty-Vec = refl
  left-unit-add-matrices addK-lUnit (x ∷ xs) =
    (ap (λ v → v ∷ add-Mat addK (repeat (repeat zero)) xs) (left-unit-add-vectors addK-lUnit x))
      ∙ ap (λ m → x ∷ m) (left-unit-add-matrices addK-lUnit xs)

  right-unit-add-matrices :
    {n m : ℕ} →
    ((x : K) → Id (addK x zero) x) →
    (v : Mat K m n) → Id (add-Mat addK v (repeat (repeat zero))) v
  right-unit-add-matrices _ empty-Vec = refl
  right-unit-add-matrices addK-lUnit (x ∷ xs) =
    (ap (λ v → v ∷ add-Mat addK xs (repeat (repeat zero))) (right-unit-add-vectors addK-lUnit x))
      ∙ ap (λ m → x ∷ m) (right-unit-add-matrices addK-lUnit xs)

  commutative-add-matrices :
    {n m : ℕ} →
    ((x y : K) → Id (addK x y) (addK y x)) →
    (a b : Mat K m n) → Id (add-Mat addK a b) (add-Mat addK b a)
  commutative-add-matrices _ empty-Vec empty-Vec = refl
  commutative-add-matrices addK-comm (a ∷ as) (b ∷ bs) =
    (ap (λ v → v ∷ (add-Mat _ as bs)) (commutative-add-vectors {zero = zero} addK-comm a b))
      ∙ ap (_∷_ (add-Vec _ b a)) (commutative-add-matrices addK-comm as bs)

  associative-add-matrices :
    {n m : ℕ} →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a b c : Mat K m n) →
    Id (add-Mat addK a (add-Mat addK b c)) (add-Mat addK (add-Mat addK a b) c)
  associative-add-matrices _ empty-Vec empty-Vec empty-Vec = refl
  associative-add-matrices addK-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    (ap (λ v → v ∷ add-Mat _ xs (add-Mat _ ys zs)) (associative-add-vectors {zero = zero} addK-assoc x y z))
      ∙ ap (_∷_ (add-Vec _ (add-Vec _ x y) z)) (associative-add-matrices addK-assoc xs ys zs)

```

## Properties of Transpose

  - transpose is its own inverse
  - (AB)ᵀ = BᵀAᵀ
  - (A+B)ᵀ = Aᵀ + Bᵀ (incomplete)
  - (kA)ᵀ = k(Aᵀ) (TODO)

```agda

-- structure borrowed from: https://gist.github.com/tomcumming/7707246
transpose-is-involution :
  {l : Level} → {K : UU l} → {m n : ℕ} →
  (x : Mat K m n) → Id x (transpose (transpose x))
transpose-is-involution {m = zero-ℕ} empty-Vec = refl
transpose-is-involution {m = succ-ℕ m} (r ∷ rs) =
  (ap (_∷_ r) (transpose-is-involution rs))
    ∙ ap-binary _∷_ (lemma-first-row r rs) (ap transpose (lemma-rest r rs))
  where
  lemma-first-row : {l : Level} → {K : UU l} → {m n : ℕ} →
                    (x : Vec K n) → (xs : Mat K m n) →
                    Id x (map head (transpose (x ∷ xs)))
  lemma-first-row {n = zero-ℕ} empty-Vec _ = refl
  lemma-first-row {n = succ-ℕ m} (k ∷ ks) xs =
    ap (_∷_ k) (lemma-first-row ks (map tail xs))

  lemma-rest : {l : Level} → {K : UU l} → {m n : ℕ} →
               (x : Vec K n) → (xs : Mat K m n) →
               Id (transpose xs) (map tail (transpose (x ∷ xs)))
  lemma-rest {n = zero-ℕ} empty-Vec xs = refl
  lemma-rest {n = succ-ℕ n} (k ∷ ks) xs =
    ap (_∷_ (map head xs))
       (lemma-rest (tail (k ∷ ks)) (map tail xs))

{-TODO:
add-transpose :
  {l : Level} → {K : UU l} → {m n : ℕ} →
  {addK : K → K → K} →
  (a b : Mat K m n) →
  Id (transpose (add-Mat addK a b)) (add-Mat addK (transpose a) (transpose b))
add-transpose {n = zero-ℕ} a b = refl
add-transpose {n = succ-ℕ _}{addK} empty-Vec empty-Vec =
  ap-binary _∷_ refl (add-transpose {addK = addK} empty-Vec empty-Vec)
add-transpose {n = succ-ℕ _}{addK} (a ∷ as) (b ∷ bs) =
  ap-binary _∷_ (lemma-first-row a b as bs) (lemma-rest a b as bs)
  where
  lemma-first-row :
    {l : Level} → {K : UU l} → {m n : ℕ} →
    {addK : K → K → K} →
    (a' b' : Vec K (succ-ℕ n)) → (as' bs' : Mat K m (succ-ℕ n)) →
    Id (map head (add-Mat addK (a' ∷ as') (b' ∷ bs')))
       (add-Vec addK (map head (a' ∷ as')) (map head (b' ∷ bs')))
  lemma-first-row {m = zero-ℕ} {n = n} {addK = addK'} (x ∷ a') (y ∷ b') empty-Vec empty-Vec = refl
  lemma-first-row {m = m} {n = n} {addK = addK'} (x ∷ a') (y ∷ b') (as' ∷ ass') (bs' ∷ bss') =
    ap-binary _∷_
      (ap head {y = addK' x y ∷ add-Vec addK' a' b'} refl)
      (lemma-first-row {addK = addK'} as' bs' ass' bss')

  lemma-rest :
    {l : Level} → {K : UU l} → {m n : ℕ} →
    {addK : K → K → K} →
    (a' b' : Vec K (succ-ℕ n)) → (as' bs' : Mat K m (succ-ℕ n)) →
    Id (transpose (tail (add-Vec addK a' b') ∷ map tail (add-Mat addK as' bs')))
       (add-Mat addK (transpose (tail a' ∷ map tail as'))
                     (transpose (tail b' ∷ map tail bs')))
  lemma-rest {m = zero-ℕ} {n = zero-ℕ} a' b' empty-Vec empty-Vec = refl
  lemma-rest {m = .zero-ℕ} {n = succ-ℕ n} (x ∷ a') (x₁ ∷ b') empty-Vec empty-Vec = {!!}
  lemma-rest {m = .(succ-ℕ _)} {n = zero-ℕ} (x ∷ a') (x₁ ∷ b') (as' ∷ as'') (bs' ∷ bs'') = {!!}
  lemma-rest {m = .(succ-ℕ _)} {n = succ-ℕ n} (x ∷ a') (x₁ ∷ b') (as' ∷ as'') (bs' ∷ bs'') = {!!}

mul-transpose :
  {l : Level} → {K : UU l} → {m n p : ℕ} →
  {addK : K → K → K} {mulK : K → K → K} {zero : K} →
  ((x y : K) → Id (mulK x y) (mulK y x)) →
  (a : Mat K m n) → (b : Mat K n p) →
  Id (transpose (mul-Mat mulK addK zero a b)) (mul-Mat mulK addK zero (transpose b) (transpose a))
mul-transpose mulK-comm empty-Vec b = {!!}
mul-transpose mulK-comm (a ∷ as) b = {!!}
-}
```
## Properties of Matrix Multiplication

 - distributive laws (incomplete)
 - associativity (TODO)
 - identity (TODO)

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {mulK : K → K → K}
  {zero : K}
  where

  left-distributive-vector-matrix :
    {n m : ℕ} →
    ({l : ℕ} →  Id (repeat {n = l} zero) (add-Vec addK (repeat zero) (repeat zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : Vec K n) (b : Mat K n m) (c : Mat K n m) →
    Id (mul-vector-matrix mulK addK zero a (add-Mat addK b c))
      (add-Vec addK (mul-vector-matrix mulK addK zero a b)
                    (mul-vector-matrix mulK addK zero a c))
  left-distributive-vector-matrix id-Vec _ _ _ empty-Vec empty-Vec empty-Vec = id-Vec
  left-distributive-vector-matrix id-Vec k-distr addK-comm addK-assoc (a ∷ as) (r1 ∷ r1s) (r2 ∷ r2s) =
      ap (λ r → add-Vec addK r (mul-vector-matrix mulK addK zero as (add-Mat addK r1s r2s)))
        (left-distributive-scalar-vector {zero = zero} k-distr a r1 r2)
        ∙ (ap (λ r → add-Vec addK (add-Vec addK (map (mulK a) r1)
                                  (mul-scalar-vector mulK a r2)) r)
              (left-distributive-vector-matrix id-Vec k-distr addK-comm addK-assoc as r1s r2s)
          ∙ lemma-shuffle)
    where
    lemma-shuffle : {n : ℕ} →
                    {x y z w : Vec K n} →
                    Id (add-Vec addK (add-Vec addK x y) (add-Vec addK z w))
                       (add-Vec addK (add-Vec addK x z) (add-Vec addK y w))
    lemma-shuffle {x = x} {y = y} {z = z} {w = w} =
      associative-add-vectors {zero = zero} addK-assoc (add-Vec addK x y) z w
        ∙ (commutative-add-vectors {zero = zero} addK-comm (add-Vec addK (add-Vec addK x y) z) w
        ∙ (associative-add-vectors {zero = zero} addK-assoc w (add-Vec addK x y) z
        ∙ (ap (λ v → add-Vec addK (add-Vec addK w v) z)
              (commutative-add-vectors {zero = zero} addK-comm x y)
        ∙ (ap (λ v → add-Vec addK v z)
              (associative-add-vectors {zero = zero} addK-assoc w y x)
        ∙ (ap (λ v → add-Vec addK (add-Vec addK v x) z)
              (commutative-add-vectors {zero = zero} addK-comm w y)
        ∙ (inv (associative-add-vectors {zero = zero} addK-assoc (add-Vec addK y w) x z)
        ∙ commutative-add-vectors {zero = zero} addK-comm (add-Vec addK y w) (add-Vec addK x z)))))))

  left-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →  Id (repeat {n = l} zero) (add-Vec addK (repeat zero) (repeat zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : Mat K m n) (b : Mat K n p) (c : Mat K n p) →
    Id (mul-Mat mulK addK zero a (add-Mat addK b c))
       (add-Mat addK (mul-Mat mulK addK zero a b)
                     (mul-Mat mulK addK zero a c))
  left-distributive-matrices _ _ _ _ empty-Vec _ _ = refl
  left-distributive-matrices id-Vec k-distr addK-comm addK-assoc (a ∷ as) b c =
    (ap (λ r → r ∷ mul-Mat mulK addK zero as (add-Mat addK b c))
        (left-distributive-vector-matrix id-Vec k-distr addK-comm addK-assoc a b c))
      ∙ ap (_∷_ (add-Vec addK (mul-vector-matrix mulK addK zero a b)
                              (mul-vector-matrix mulK addK zero a c)))
          (left-distributive-matrices id-Vec k-distr addK-comm addK-assoc as b c)

{- TODO: right distributivity
  right-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →  Id (repeat {n = l} zero) (add-Vec addK (repeat zero) (repeat zero))) →
    ((x y z : K) → (Id (mulK (addK x y) z) (addK (mulK x z) (mulK y z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (b : Mat K n p) (c : Mat K n p) (d : Mat K p m) →
    Id (mul-Mat mulK addK zero (add-Mat addK b c) d)
       (add-Mat addK (mul-Mat mulK addK zero b d)
                     (mul-Mat mulK addK zero c d))
  right-distributive-matrices _ _ _ _ empty-Vec empty-Vec _ = refl
  right-distributive-matrices {p = .zero-ℕ} id-Vec k-distr addK-comm addK-assoc (b ∷ bs) (c ∷ cs) empty-Vec = {!!}
  right-distributive-matrices id-Vec k-distr addK-comm addK-assoc (b ∷ bs) (c ∷ cs) (d ∷ ds) = {!!}
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
