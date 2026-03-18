# Quotient algebras

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.quotient-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.action-on-identifications-functions
open import foundation.unit-type
open import foundation.raising-universe-levels
open import foundation.identity-types
open import foundation.function-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.finite-sequences-set-quotients
open import foundation.functoriality-set-quotients
open import foundation.functoriality-propositional-truncation
open import foundation.reflecting-maps-equivalence-relations
open import lists.functoriality-tuples
open import foundation.universal-property-set-quotients
open import foundation.multivariable-functoriality-set-quotients
open import lists.set-quotients-tuples
open import foundation.multivariable-operations
open import foundation.propositional-truncations
open import lists.equivalence-relations-finite-sequences
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import lists.tuples
open import lists.finite-sequences
open import lists.equivalence-relations-tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.congruences
open import universal-algebra.terms-over-signatures
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

The
{{#concept "quotient" Disambiguation="of an algebra of an algebraic theory, single-sorted, finitary" WD="quotient algebra" WDID=Q2589508}}
of an [algebra](universal-algebra.algebras.md) by a
[congruence](universal-algebra.congruences.md) is the
[set quotient](foundation.set-quotients.md) by that congruence. This quotient
again has the structure of an algebra inherited by the original one.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  ((R , preserves-sim-op-R) : congruence-Algebra l4 σ T A)
  where

  set-quotient-Algebra : Set (l3 ⊔ l4)
  set-quotient-Algebra = quotient-Set R

  type-quotient-Algebra : UU (l3 ⊔ l4)
  type-quotient-Algebra = set-quotient R

  hom-is-model-quotient-Algebra :
    (op : operation-signature σ) →
    hom-equivalence-relation
      ( equivalence-relation-tuple R (arity-operation-signature σ op))
      ( R)
  hom-is-model-quotient-Algebra op =
    ( is-model-set-Algebra σ T A op ,
      preserves-sim-op-R op)

  quotient-map-Algebra : type-Algebra σ T A → type-quotient-Algebra
  quotient-map-Algebra = quotient-map R

  opaque
    is-model-quotient-Algebra : is-model-of-signature σ set-quotient-Algebra
    is-model-quotient-Algebra op =
      let
        k = arity-operation-signature σ op
      in
        map-is-set-quotient
          ( equivalence-relation-tuple R k)
          ( tuple-Set set-quotient-Algebra k)
          ( reflecting-map-tuple-quotient-map R k)
          ( R)
          ( set-quotient-Algebra)
          ( reflecting-map-quotient-map R)
          ( is-set-quotient-tuple-set-quotient R k)
          ( is-set-quotient-set-quotient R)
          ( hom-is-model-quotient-Algebra op)

  model-of-signature-quotient-Algebra :
    Model-Of-Signature (l3 ⊔ l4) σ
  model-of-signature-quotient-Algebra =
    ( set-quotient-Algebra ,
      is-model-quotient-Algebra)

  abstract opaque
    unfolding is-model-quotient-Algebra

    compute-is-model-quotient-Algebra :
      (op : operation-signature σ)
      (t : tuple (type-Algebra σ T A) (arity-operation-signature σ op)) →
      is-model-quotient-Algebra op (map-tuple quotient-map-Algebra t) ＝
      quotient-map-Algebra (is-model-set-Algebra σ T A op t)
    compute-is-model-quotient-Algebra op =
      let
        k = arity-operation-signature σ op
      in
        coherence-square-map-is-set-quotient
          ( equivalence-relation-tuple R k)
          ( tuple-Set set-quotient-Algebra k)
          ( reflecting-map-tuple-quotient-map R k)
          ( R)
          ( set-quotient-Algebra)
          ( reflecting-map-quotient-map R)
          ( is-set-quotient-tuple-set-quotient R k)
          ( is-set-quotient-set-quotient R)
          ( hom-is-model-quotient-Algebra op)

  abstract
    compute-eval-term-quotient-Algebra :
      {n : ℕ} (t : term σ n) (v : fin-sequence (type-Algebra σ T A) n) →
      eval-term σ is-model-quotient-Algebra (quotient-map-Algebra ∘ v) t ＝
      quotient-map-Algebra
        ( eval-term σ (is-model-set-Algebra σ T A) v t)

    compute-eval-tuple-term-quotient-Algebra :
      {n k : ℕ} (t : tuple (term σ n) k)
      (v : fin-sequence (type-Algebra σ T A) n) →
      Eq-tuple
        ( k)
        ( eval-tuple-term
          ( σ)
          ( is-model-quotient-Algebra)
          ( quotient-map-Algebra ∘ v)
          ( t))
        ( map-tuple
          ( quotient-map-Algebra)
          ( eval-tuple-term σ (is-model-set-Algebra σ T A) v t))

    compute-eval-term-quotient-Algebra (var-term i) v = refl
    compute-eval-term-quotient-Algebra (op-term op xs) v =
      equational-reasoning
        is-model-quotient-Algebra op
          ( eval-tuple-term
            ( σ)
            ( is-model-quotient-Algebra)
            ( quotient-map-Algebra ∘ v) xs)
        ＝
          is-model-quotient-Algebra op
            ( map-tuple
              ( quotient-map-Algebra)
              ( eval-tuple-term σ (is-model-set-Algebra σ T A) v xs))
          by
            ap
              ( is-model-quotient-Algebra op)
              ( eq-Eq-tuple _ _ _
                ( compute-eval-tuple-term-quotient-Algebra xs v))
        ＝
          quotient-map-Algebra
            ( is-model-set-Algebra σ T A
              ( op)
              ( eval-tuple-term σ (is-model-set-Algebra σ T A) v xs))
          by compute-is-model-quotient-Algebra op _

    compute-eval-tuple-term-quotient-Algebra empty-tuple v =
      map-raise star
    compute-eval-tuple-term-quotient-Algebra (t ∷ ts) v =
      ( compute-eval-term-quotient-Algebra t v ,
        compute-eval-tuple-term-quotient-Algebra ts v)

    is-algebra-quotient-Algebra :
      is-algebra-Model-of-Signature σ T model-of-signature-quotient-Algebra
    is-algebra-quotient-Algebra i v =
      ind-is-set-quotient
        {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}
```
