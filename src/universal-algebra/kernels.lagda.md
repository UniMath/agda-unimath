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
open import universal-algebra.algebras-of-algebraic-theories
open import universal-algebra.congruences
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.signatures
```

</details>

## Idea

The
{{#concept "kernel" Disambiguation="of a homomorphism of algebras of an algebraic theory, single-sorted, finitary" WD="kernel" WDID=Q574844 Agda=kernel-hom-Algebra}}
of a [homomorphism](universal-algebra.homomorphisms-of-algebras.md) `f` of
[algebras](universal-algebra.algebras-of-algebraic-theories.md) is the
[congruence relation](universal-algebra.congruences.md) given by `x ~ y` iff
`f x ~ f y`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (B : Algebra l4 σ T)
  (F : hom-Algebra σ T A B)
  where

  rel-prop-kernel-hom-Algebra :
    Relation-Prop l4 (type-Algebra σ T A)
  pr1 (rel-prop-kernel-hom-Algebra x y) =
    map-hom-Algebra σ T A B F x ＝ map-hom-Algebra σ T A B F y
  pr2 (rel-prop-kernel-hom-Algebra x y) =
    is-set-type-Algebra σ T B _ _

  equivalence-relation-kernel-hom-Algebra :
    equivalence-relation l4 (type-Algebra σ T A)
  pr1 equivalence-relation-kernel-hom-Algebra =
    rel-prop-kernel-hom-Algebra
  pr1 (pr2 equivalence-relation-kernel-hom-Algebra) _ = refl
  pr1 (pr2 (pr2 equivalence-relation-kernel-hom-Algebra)) _ _ = inv
  pr2 (pr2 (pr2 equivalence-relation-kernel-hom-Algebra)) _ _ _ f g = g ∙ f

  kernel-hom-Algebra :
    congruence-Algebra σ T A l4
  pr1 kernel-hom-Algebra =
    equivalence-relation-kernel-hom-Algebra
  pr2 kernel-hom-Algebra op v v' p =
    equational-reasoning
      f (is-model-set-Algebra σ T A op v)
      ＝ is-model-set-Algebra σ T B op (map-tuple f v)
        by preserves-operations-hom-Algebra σ T A B F op v
      ＝ is-model-set-Algebra σ T B op (map-tuple f v')
        by
          ap
            ( is-model-set-Algebra σ T B op)
            ( map-hom-Algebra-lemma (pr2 σ op) v v' p)
      ＝ f (is-model-set-Algebra σ T A op v')
        by inv (preserves-operations-hom-Algebra σ T A B F op v')
    where
    f = map-hom-Algebra σ T A B F
    map-hom-Algebra-lemma :
      ( n : ℕ) →
      ( v v' : tuple (type-Algebra σ T A) n) →
      ( relation-holds-all-tuple σ T A
        equivalence-relation-kernel-hom-Algebra v v') →
      (map-tuple f v) ＝ (map-tuple f v')
    map-hom-Algebra-lemma zero-ℕ empty-tuple empty-tuple p =
      refl
    map-hom-Algebra-lemma (succ-ℕ n) (x ∷ v) (x' ∷ v') (p , p') =
      ap-binary (_∷_) p (map-hom-Algebra-lemma n v v' p')
```
