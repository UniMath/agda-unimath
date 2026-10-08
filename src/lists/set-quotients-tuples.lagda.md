# Set quotients of tuples

```agda
module lists.set-quotients-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import lists.equivalence-relations-tuples
open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

Given an [equivalence relation](foundation.equivalence-relations.md) `R` on a
type `A`, the type of `n`-[tuples](lists.tuples.md) in the
[set quotient](foundation.set-quotients.md) `A/R` satisfies the
[universal property of the set quotient](foundation.universal-property-set-quotients.md)
on the
[equivalence relation induced by `R` on `n`-tuples in A](lists.equivalence-relations-tuples.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : equivalence-relation l2 A)
  where

  tuple-set-quotient : (n : ℕ) → UU (l1 ⊔ l2)
  tuple-set-quotient n = tuple (set-quotient R) n

  abstract
    reflects-equivalence-relation-map-tuple-quotient-map :
      (n : ℕ) →
      reflects-equivalence-relation
        ( equivalence-relation-tuple R n)
        ( map-tuple (quotient-map R))
    reflects-equivalence-relation-map-tuple-quotient-map
      0 {empty-tuple} {empty-tuple} _ =
      refl
    reflects-equivalence-relation-map-tuple-quotient-map
      (succ-ℕ n) {x ∷ xs} {y ∷ ys} (x~y , xs~ys) =
      eq-Eq-tuple _ _ _
        ( apply-effectiveness-quotient-map' R x~y ,
          Eq-eq-tuple _ _ _
            ( reflects-equivalence-relation-map-tuple-quotient-map n xs~ys))

    is-surjective-map-tuple-quotient-map :
      (n : ℕ) →
      is-surjective (map-tuple {n = n} (quotient-map R))
    is-surjective-map-tuple-quotient-map 0 empty-tuple =
      intro-exists empty-tuple refl
    is-surjective-map-tuple-quotient-map (succ-ℕ n) (qx ∷ qxs) =
      map-binary-trunc-Prop
        ( λ (x , Qx) (xs , Qxs) →
          ( x ∷ xs , eq-Eq-tuple _ _ _ ( Qx , Eq-eq-tuple _ _ _ Qxs)))
        ( is-surjective-quotient-map R qx)
        ( is-surjective-map-tuple-quotient-map n qxs)

    apply-effectiveness-map-tuple-quotient-map :
      (n : ℕ) (x y : tuple A n) →
      map-tuple (quotient-map R) x ＝ map-tuple (quotient-map R) y →
      sim-equivalence-relation-tuple R n x y
    apply-effectiveness-map-tuple-quotient-map 0 empty-tuple empty-tuple refl =
      map-raise star
    apply-effectiveness-map-tuple-quotient-map
      (succ-ℕ n) (x ∷ xs) (y ∷ ys) qxs=qys =
      ( apply-effectiveness-quotient-map R (ap head-tuple qxs=qys) ,
        apply-effectiveness-map-tuple-quotient-map
          ( n)
          ( xs)
          ( ys)
          ( ap tail-tuple qxs=qys))

    is-effective-map-tuple-quotient-map :
      (n : ℕ) →
      is-effective
        ( equivalence-relation-tuple R n)
        ( map-tuple (quotient-map R))
    is-effective-map-tuple-quotient-map n xs ys =
      equiv-iff
        ( Id-Prop
          ( tuple-Set (quotient-Set R) n)
          ( map-tuple (quotient-map R) xs)
          ( map-tuple (quotient-map R) ys))
        ( sim-prop-equivalence-relation-tuple R n xs ys)
        ( apply-effectiveness-map-tuple-quotient-map n xs ys)
        ( reflects-equivalence-relation-map-tuple-quotient-map n)

  reflecting-map-tuple-quotient-map :
    (n : ℕ) →
    reflecting-map-equivalence-relation
      ( equivalence-relation-tuple R n)
      ( tuple-set-quotient n)
  reflecting-map-tuple-quotient-map n =
    ( map-tuple (quotient-map R) ,
      reflects-equivalence-relation-map-tuple-quotient-map n)

  abstract
    is-set-quotient-tuple-set-quotient :
      (n : ℕ) →
      is-set-quotient
        ( equivalence-relation-tuple R n)
        ( tuple-Set (quotient-Set R) n)
        ( reflecting-map-tuple-quotient-map n)
    is-set-quotient-tuple-set-quotient n =
      is-set-quotient-is-surjective-and-effective
        ( equivalence-relation-tuple R n)
        ( tuple-Set (quotient-Set R) n)
        ( reflecting-map-tuple-quotient-map n)
        ( is-surjective-map-tuple-quotient-map n ,
          is-effective-map-tuple-quotient-map n)
```
