# Quotient algebras

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.quotient-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-homotopies-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-set-quotients
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import lists.equivalence-relations-finite-sequences
open import lists.equivalence-relations-tuples
open import lists.finite-sequences
open import lists.functoriality-tuples
open import lists.set-quotients-finite-sequences
open import lists.set-quotients-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.congruences
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
open import universal-algebra.universal-property-quotient-algebras
```

</details>

## Idea

The
{{#concept "quotient" Disambiguation="of an algebra of an algebraic theory, single-sorted, finitary" WD="quotient algebra" WDID=Q2589508}}
of an [algebra](universal-algebra.algebras.md) by a
[congruence](universal-algebra.congruences.md) is the
[set quotient](foundation.set-quotients.md) by that congruence. This quotient
again has the structure of an algebra inherited by the original one, and
satisfies the
[universal property](universal-algebra.universal-property-quotient-algebras.md)
of quotient algebras.

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

  model-quotient-Algebra :
    Model-Of-Signature (l3 ⊔ l4) σ
  model-quotient-Algebra =
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
      ( ap
        ( is-model-quotient-Algebra op)
        ( eq-Eq-tuple _ _ _
          ( compute-eval-tuple-term-quotient-Algebra xs v))) ∙
      ( compute-is-model-quotient-Algebra op _)

    compute-eval-tuple-term-quotient-Algebra empty-tuple v =
      map-raise star
    compute-eval-tuple-term-quotient-Algebra (t ∷ ts) v =
      ( compute-eval-term-quotient-Algebra t v ,
        compute-eval-tuple-term-quotient-Algebra ts v)

    is-algebra-model-quotient-Algebra :
      is-algebra-Model-of-Signature σ T model-quotient-Algebra
    is-algebra-model-quotient-Algebra i =
      let
        eq@(k , lhs , rhs) = index-abstract-equation-Algebraic-Theory σ T i
      in
        ind-is-set-quotient
          ( fin-sequence-equivalence-relation R k)
          ( fin-sequence-Set set-quotient-Algebra k)
          ( reflecting-quotient-map-fin-sequence R k)
          ( is-set-quotient-fin-sequence-set-quotient R k)
          ( satisfies-equation-assignment-prop-Model-Of-Signature
            ( σ)
            ( eq)
            ( model-quotient-Algebra))
          ( λ v →
            ( compute-eval-term-quotient-Algebra lhs v) ∙
            ( ap
              ( quotient-map-Algebra)
              ( is-algebra-model-Algebra σ T A i v)) ∙
            ( inv (compute-eval-term-quotient-Algebra rhs v)))

  quotient-Algebra : Algebra (l3 ⊔ l4) σ T
  quotient-Algebra =
    ( model-quotient-Algebra , is-algebra-model-quotient-Algebra)
```

## Properties

### The quotient map is a homomorphism

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R@(equiv-rel-R , _) : congruence-Algebra l4 σ T A)
  where

  preserves-operations-quotient-map-Algebra :
    preserves-operations-Algebra σ T
      ( A)
      ( quotient-Algebra σ T A R)
      ( quotient-map-Algebra σ T A R)
  preserves-operations-quotient-map-Algebra op xs =
    inv (compute-is-model-quotient-Algebra σ T A R op xs)

  hom-quotient-map-Algebra :
    hom-Algebra σ T A (quotient-Algebra σ T A R)
  hom-quotient-map-Algebra =
    ( quotient-map-Algebra σ T A R ,
      preserves-operations-quotient-map-Algebra)

  reflecting-congruence-hom-quotient-map-Algebra :
    reflecting-congruence-hom-Algebra σ T A R (quotient-Algebra σ T A R)
  reflecting-congruence-hom-quotient-map-Algebra =
    ( hom-quotient-map-Algebra ,
      apply-effectiveness-quotient-map' equiv-rel-R)
```

### The quotient algebra satisfies the universal property of quotient algebras

#### The homomorphism from `(A/R) → B` induced by a homomorphism `A → B` reflecting the congruence `R`

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R@(equiv-rel-R , _) : congruence-Algebra l4 σ T A)
  (B : Algebra l5 σ T)
  where

  map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra :
    reflecting-congruence-hom-Algebra σ T A R B →
    set-quotient equiv-rel-R → type-Algebra σ T B
  map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
    ( (φ , preserves-ops-φ) , reflects-R-φ) =
    inv-precomp-set-quotient
      ( equiv-rel-R)
      ( set-Algebra σ T B)
      ( φ , reflects-R-φ)

  abstract
    is-hom-map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra :
      (φ : reflecting-congruence-hom-Algebra σ T A R B) →
      preserves-operations-Algebra σ T (quotient-Algebra σ T A R) B
        ( map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra φ)
    is-hom-map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
      refl-φ@((φ , preserves-ops-φ) , reflects-R-φ) op =
      let
        k = arity-operation-signature σ op
      in
        ind-is-set-quotient
          ( equivalence-relation-tuple equiv-rel-R k)
          ( tuple-Set (quotient-Set equiv-rel-R) k)
          ( reflecting-map-tuple-quotient-map equiv-rel-R k)
          ( is-set-quotient-tuple-set-quotient equiv-rel-R k)
          ( λ xs →
            Id-Prop
              ( set-Algebra σ T B)
              ( map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
                ( refl-φ)
                ( is-model-quotient-Algebra σ T A R op xs))
              ( is-model-set-Algebra σ T B
                ( op)
                ( map-tuple
                  ( map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
                    ( refl-φ))
                  ( xs))))
          ( λ xs →
            equational-reasoning
              map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
                ( refl-φ)
                ( is-model-quotient-Algebra σ T A R op
                  ( map-tuple (quotient-map equiv-rel-R) xs))
              ＝
                map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
                  ( refl-φ)
                  ( quotient-map
                    ( equiv-rel-R)
                    ( is-model-set-Algebra σ T A op xs))
                by
                  ap
                    ( map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
                      ( refl-φ))
                    ( compute-is-model-quotient-Algebra σ T A R op xs)
              ＝ φ (is-model-set-Algebra σ T A op xs)
                by
                  is-section-inv-precomp-set-quotient
                    ( equiv-rel-R)
                    ( set-Algebra σ T B)
                    ( φ , reflects-R-φ)
                    ( is-model-set-Algebra σ T A op xs)
              ＝ is-model-set-Algebra σ T B op (map-tuple φ xs)
                by preserves-ops-φ op xs
              ＝
                is-model-set-Algebra σ T B op
                  ( map-tuple
                    ( ( map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
                        ( refl-φ)) ∘
                      ( quotient-map equiv-rel-R))
                    ( xs))
                by
                  action-htpy-function
                    ( λ f → is-model-set-Algebra σ T B op (map-tuple f xs))
                    ( inv-htpy
                      ( is-section-inv-precomp-set-quotient
                        ( equiv-rel-R)
                        ( set-Algebra σ T B)
                        ( φ , reflects-R-φ)))
              ＝
                is-model-set-Algebra σ T B op
                  ( map-tuple
                    ( map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
                      ( refl-φ))
                      ( map-tuple (quotient-map equiv-rel-R) xs))
                by
                  action-htpy-function
                    ( λ f → is-model-set-Algebra σ T B op (f xs))
                    ( inv-htpy (preserves-comp-map-tuple k _ _)))
```

### Precomposition with the homomorphism from `A → A/R` is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R@(equiv-rel-R , _) : congruence-Algebra l4 σ T A)
  where

  abstract
    is-quotient-algebra-quotient-Algebra :
      is-quotient-Algebra σ T A R
        ( quotient-Algebra σ T A R)
        ( reflecting-congruence-hom-quotient-map-Algebra σ T A R)
    is-quotient-algebra-quotient-Algebra B =
      is-equiv-comp _ _
        ( is-equiv-subtype-is-equiv'
          ( is-prop-preserves-operations-Algebra σ T
            ( quotient-Algebra σ T A R)
            ( B))
          ( ( is-prop-preserves-operations-Algebra σ T A B) ∘
            ( map-reflecting-map-equivalence-relation equiv-rel-R))
          ( precomp-Set-Quotient
            ( equiv-rel-R)
            ( quotient-Set equiv-rel-R)
            ( reflecting-map-quotient-map equiv-rel-R)
            ( set-Algebra σ T B))
          ( λ f preserves-ops-f →
            preserves-operations-map-comp-hom-Algebra σ T
              ( A)
              ( quotient-Algebra σ T A R)
              ( B)
              ( f , preserves-ops-f)
              ( hom-quotient-map-Algebra σ T A R))
          ( is-set-quotient-set-quotient equiv-rel-R (set-Algebra σ T B))
          ( λ (f , reflects-R-f) preserves-ops-f →
            is-hom-map-hom-inv-precomp-is-quotient-algebra-quotient-Algebra
              ( σ)
              ( T)
              ( A)
              ( R)
              ( B)
              ( (f , preserves-ops-f) , reflects-R-f)))
        ( is-equiv-map-right-swap-Σ)
```
