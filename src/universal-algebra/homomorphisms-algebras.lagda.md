# Homomorphisms of algebras

```agda
module universal-algebra.homomorphisms-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-theories
open import universal-algebra.signatures
```

</details>

## Idea

An algebra homomorphism from one algebra to another is function between their
underlying types such that all the structure is preserved.

## Definitions

```agda
module _
  { l1 : Level} ( Sig : signature l1)
  { l2 : Level } ( Th : Theory Sig l2)
  { l3 l4 : Level }
  ( Alg1 : Algebra Sig Th l3)
  ( Alg2 : Algebra Sig Th l4)
  where

  preserves-ops-Algebra :
    (type-Algebra Sig Th Alg1 → type-Algebra Sig Th Alg2) →
    UU (l1 ⊔ l3 ⊔ l4)
  preserves-ops-Algebra f =
    ( op : operations-signature Sig) →
    ( v : vec (type-Algebra Sig Th Alg1)
      ( arity-operations-signature Sig op)) →
        ( f (is-model-set-Algebra Sig Th Alg1 op v) ＝
          ( is-model-set-Algebra Sig Th Alg2 op (map-vec f v)))

  type-hom-Algebra : UU (l1 ⊔ l3 ⊔ l4)
  type-hom-Algebra =
    Σ ( type-Algebra Sig Th Alg1 → type-Algebra Sig Th Alg2)
      ( preserves-ops-Algebra)

  map-hom-Algebra :
    type-hom-Algebra →
    type-Algebra Sig Th Alg1 →
    type-Algebra Sig Th Alg2
  map-hom-Algebra = pr1

  preserves-ops-hom-Algebra :
    ( f : type-hom-Algebra) →
    preserves-ops-Algebra (map-hom-Algebra f)
  preserves-ops-hom-Algebra = pr2
```
