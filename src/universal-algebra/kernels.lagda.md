# Kernels of homomorphisms of algebras

```agda
module universal-algebra.kernels where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.universe-levels

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.congruences
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.signatures
```

</details>

## Idea

The kernel of a homomorphism `f` of algebras is the congruence relation given by
`x ~ y` iff `f x ~ f y`.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 : Level}
  ( Alg1 : Algebra Sg Th l3)
  ( Alg2 : Algebra Sg Th l4)
  ( F : hom-Algebra Sg Th Alg1 Alg2)
  where

  rel-prop-kernel-hom-Algebra :
    Relation-Prop l4 (type-Algebra Sg Th Alg1)
  pr1 (rel-prop-kernel-hom-Algebra x y) =
    map-hom-Algebra Sg Th Alg1 Alg2 F x ＝
      map-hom-Algebra Sg Th Alg1 Alg2 F y
  pr2 (rel-prop-kernel-hom-Algebra x y) =
    is-set-Algebra Sg Th Alg2 _ _

  equivalence-relation-kernel-hom-Algebra :
    equivalence-relation l4 (type-Algebra Sg Th Alg1)
  pr1 equivalence-relation-kernel-hom-Algebra =
    rel-prop-kernel-hom-Algebra
  pr1 (pr2 equivalence-relation-kernel-hom-Algebra) _ = refl
  pr1 (pr2 (pr2 equivalence-relation-kernel-hom-Algebra)) _ _ = inv
  pr2 (pr2 (pr2 equivalence-relation-kernel-hom-Algebra)) _ _ _ f g = g ∙ f

  kernel-hom-Algebra :
    congruence-Algebra Sg Th Alg1 l4
  pr1 kernel-hom-Algebra = equivalence-relation-kernel-hom-Algebra
  pr2 kernel-hom-Algebra op v v' p =
    equational-reasoning
      f (is-model-set-Algebra Sg Th Alg1 op v)
      ＝ is-model-set-Algebra Sg Th Alg2 op (map-tuple f v)
        by preserves-operations-hom-Algebra Sg Th Alg1 Alg2 F op v
      ＝ is-model-set-Algebra Sg Th Alg2 op (map-tuple f v')
        by
          ap
            ( is-model-set-Algebra Sg Th Alg2 op)
            ( map-hom-Algebra-lemma (pr2 Sg op) v v' p)
      ＝ f (is-model-set-Algebra Sg Th Alg1 op v')
        by inv (preserves-operations-hom-Algebra Sg Th Alg1 Alg2 F op v')
    where
    f = map-hom-Algebra Sg Th Alg1 Alg2 F
    map-hom-Algebra-lemma :
      ( n : ℕ) →
      ( v v' : tuple (type-Algebra Sg Th Alg1) n) →
      ( relation-holds-all-tuple Sg Th Alg1
        equivalence-relation-kernel-hom-Algebra v v') →
      (map-tuple f v) ＝ (map-tuple f v')
    map-hom-Algebra-lemma zero-ℕ empty-tuple empty-tuple p = refl
    map-hom-Algebra-lemma (succ-ℕ n) (x ∷ v) (x' ∷ v') (p , p') =
      ap-binary (_∷_) p (map-hom-Algebra-lemma n v v' p')
```
