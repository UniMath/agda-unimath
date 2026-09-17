# The algebra of differentiable maps from proper closed intervals in the real numbers to normed real algebras

```agda
module functional-analysis.algebra-of-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.function-algebras-commutative-rings
open import commutative-algebra.subalgebras-commutative-rings
open import commutative-algebra.subsets-algebras-commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras
open import functional-analysis.multiplication-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras
open import functional-analysis.vector-space-of-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.normed-real-algebras
open import linear-algebra.real-algebras

open import real-numbers.large-ring-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
```

</details>

## Idea

The
[differentiable maps](functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras.md)
from a [closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` in the [real numbers](real-numbers.dedekind-real-numbers.md) to a
[normed real algebra](linear-algebra.normed-real-algebras.md) themselves form an
[algebra over the real numbers](linear-algebra.real-algebras.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (let nvs-A = normed-vector-space-Normed-ℝ-Algebra A)
  where

  is-differentiable-const-zero-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
      ( A)
      ( [a,b])
      ( λ _ → zero-Normed-ℝ-Algebra A)
  is-differentiable-const-zero-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-differentiable-const-zero-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( nvs-A)
      ( [a,b])

  is-closed-under-addition-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-closed-under-addition-subset-algebra-Commutative-Ring
      ( commutative-ring-ℝ l1)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l1)
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( algebra-Normed-ℝ-Algebra A))
      ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra
        ( A)
        ( [a,b]))
  is-closed-under-addition-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-closed-under-addition-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( nvs-A)
      ( [a,b])

  is-closed-under-scalar-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-closed-under-scalar-multiplication-subset-algebra-Commutative-Ring
      ( commutative-ring-ℝ l1)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l1)
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( algebra-Normed-ℝ-Algebra A))
      ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra
        ( A)
        ( [a,b]))
  is-closed-under-scalar-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-closed-under-scalar-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( nvs-A)
      ( [a,b])

  is-closed-under-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-closed-under-multiplication-subset-algebra-Commutative-Ring
      ( commutative-ring-ℝ l1)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l1)
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( algebra-Normed-ℝ-Algebra A))
      ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra
        ( A)
        ( [a,b]))
  is-closed-under-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
    f g Df Dg =
    is-differentiable-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
      ( A)
      ( [a,b])
      ( mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
        ( A)
        ( [a,b])
        ( f , Df)
        ( g , Dg))

  is-subalgebra-is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-subalgebra-subset-algebra-Commutative-Ring
      ( commutative-ring-ℝ l1)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l1)
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( algebra-Normed-ℝ-Algebra A))
      ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra
        ( A)
        ( [a,b]))
  is-subalgebra-is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    ( is-differentiable-const-zero-map-proper-closed-interval-real-Normed-ℝ-Algebra ,
      is-closed-under-addition-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra ,
      is-closed-under-scalar-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra ,
      is-closed-under-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)

  subalgebra-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    subalgebra-Commutative-Ring
      ( lsuc l1 ⊔ l2)
      ( commutative-ring-ℝ l1)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l1)
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( algebra-Normed-ℝ-Algebra A))
  subalgebra-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra
        ( A)
        ( [a,b]) ,
      is-subalgebra-is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra)

  algebra-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    ℝ-Algebra l1 (lsuc l1 ⊔ l2)
  algebra-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    algebra-subalgebra-Commutative-Ring
      ( commutative-ring-ℝ l1)
      ( function-algebra-Commutative-Ring
        ( commutative-ring-ℝ l1)
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( algebra-Normed-ℝ-Algebra A))
      ( subalgebra-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
```
