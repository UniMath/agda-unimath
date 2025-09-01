# Deloopings of the sign homomorphism

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.delooping-sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-type-groups
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

open import foundation.action-on-equivalences-type-families-over-subuniverses
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-extensionality
open import foundation.equivalence-induction
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.uniqueness-set-quotients
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import group-theory.concrete-groups
open import group-theory.generating-sets-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-generated-subgroups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.symmetric-groups

open import synthetic-homotopy-theory.loop-spaces

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.set-quotients-of-index-two
open import univalent-combinatorics.standard-finite-types
```

</details>

## Ideas

The delooping of a group homomorphism `f : G → H` is a pointed map
`Bf : BG → BH` equipped with a homotopy witnessing that the following square
commutes :

```text
        f
  G --------> H
  |           |
 ≅|           |≅
  |           |
  ∨           ∨
  BG ------> BH
       ΩBf
```

In this file, we study the delooping of the sign homomorphism, and, more
precisely, how to detect that a pointed map between `BSn` and `BS2` is a
delooping of the sign homomorphism.

## Definition

### Construction of the delooping of the sign homomorphism with quotients (Corollary 25)

```agda
module _
  { l1 l2 l3 : Level}
  ( D : (n : ℕ) (X : Type-With-Cardinality-ℕ l1 n) → UU l2)
  ( R :
    (n : ℕ) (X : Type-With-Cardinality-ℕ l1 n) →
    equivalence-relation l3 (D n X))
  ( is-decidable-R :
    (n : ℕ) → leq-ℕ 2 n → (X : Type-With-Cardinality-ℕ l1 n)
    (a b : D n X) → is-decidable (sim-equivalence-relation (R n X) a b))
  ( equiv-D/R-fin-2-equiv :
    (n : ℕ) (X : Type-With-Cardinality-ℕ l1 n) →
    leq-ℕ 2 n → Fin n ≃ type-Type-With-Cardinality-ℕ n X →
    Fin 2 ≃ equivalence-class (R n X))
  ( quotient-aut-succ-succ-Fin : (n : ℕ) →
    ( raise-Fin l1 (n +ℕ 2) ≃ raise-Fin l1 (n +ℕ 2)) →
    D ( n +ℕ 2)
      ( raise-Fin l1 (n +ℕ 2) ,
        unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2))))
  ( not-R-transposition-fin-succ-succ : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l1 (raise-Fin l1 (n +ℕ 2))) →
    ¬ ( sim-equivalence-relation
      ( R
        ( n +ℕ 2)
        ( raise-Fin l1 (n +ℕ 2) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2))))
      ( quotient-aut-succ-succ-Fin n (transposition Y))
      ( map-equiv
        ( action-equiv-family-over-subuniverse
          ( mere-equiv-Prop (Fin (n +ℕ 2)))
          ( D (n +ℕ 2))
          ( raise l1 (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
          ( raise l1 (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
          ( transposition Y))
        ( quotient-aut-succ-succ-Fin n (transposition Y)))))
  where

  private
    l4 : Level
    l4 = l2 ⊔ lsuc l3

    eq-counting-equivalence-class-R :
      (n : ℕ) →
      equivalence-class
        ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))) ＝
      raise (l2 ⊔ lsuc l3) (Fin 2)
    eq-counting-equivalence-class-R n =
      eq-equiv
        ( compute-raise-Fin l4 2 ∘e
          inv-equiv
            ( equiv-D/R-fin-2-equiv
              ( n +ℕ 2)
              ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
              ( star)
              ( compute-raise-Fin l1 (n +ℕ 2))))

    invertible-action-D-equiv :
      (n : ℕ) (X X' : Type-With-Cardinality-ℕ l1 n) →
      type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X' →
      D n X ≃ D n X'
    invertible-action-D-equiv n =
      action-equiv-family-over-subuniverse (mere-equiv-Prop (Fin n)) (D n)

    preserves-id-equiv-invertible-action-D-equiv :
      (n : ℕ) (X : Type-With-Cardinality-ℕ l1 n) →
      invertible-action-D-equiv n X X id-equiv ＝ id-equiv
    preserves-id-equiv-invertible-action-D-equiv n =
      compute-id-equiv-action-equiv-family-over-subuniverse
        ( mere-equiv-Prop (Fin n))
        ( D n)

    abstract
      preserves-R-invertible-action-D-equiv :
        ( n : ℕ) →
        ( X X' : Type-With-Cardinality-ℕ l1 n)
        ( e :
          type-Type-With-Cardinality-ℕ n X ≃
          type-Type-With-Cardinality-ℕ n X') →
        ( a a' : D n X) →
        ( sim-equivalence-relation (R n X) a a' ↔
          sim-equivalence-relation
            ( R n X')
            ( map-equiv (invertible-action-D-equiv n X X' e) a)
            ( map-equiv (invertible-action-D-equiv n X X' e) a'))
      preserves-R-invertible-action-D-equiv n X =
        ind-equiv-subuniverse
          ( mere-equiv-Prop (Fin n))
          ( X)
          ( λ Y f →
            ( a a' : D n X) →
            ( sim-equivalence-relation (R n X) a a' ↔
              sim-equivalence-relation
                ( R n Y)
                ( map-equiv (invertible-action-D-equiv n X Y f) a)
                ( map-equiv (invertible-action-D-equiv n X Y f) a')))
          ( λ a a' →
            ( binary-tr
              ( sim-equivalence-relation (R n X))
                ( inv
                  ( htpy-eq-equiv
                    ( preserves-id-equiv-invertible-action-D-equiv n X)
                    ( a)))
                ( inv
                  ( htpy-eq-equiv
                    ( preserves-id-equiv-invertible-action-D-equiv n X)
                    ( a')))) ,
            ( binary-tr
              ( sim-equivalence-relation (R n X))
                ( htpy-eq-equiv
                  ( preserves-id-equiv-invertible-action-D-equiv n X)
                  ( a))
                ( htpy-eq-equiv
                  ( preserves-id-equiv-invertible-action-D-equiv n X)
                  ( a'))))
    that-thing :
      (n : ℕ) →
      Fin 2 ≃
      equivalence-class
        ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
    that-thing n =
      equiv-D/R-fin-2-equiv
        ( n +ℕ 2)
        ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
        ( star)
        ( compute-raise-Fin l1 (n +ℕ 2))

    quotient-loop-Fin :
      (n : ℕ) → type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))) →
      ( D (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)) ≃
        D (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
    quotient-loop-Fin n p =
      invertible-action-D-equiv
        ( n +ℕ 2)
        ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
        ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( p))

    map-quotient-loop-Fin :
      (n : ℕ) → type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))) →
      D (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)) →
      D (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
    map-quotient-loop-Fin n p =
      map-equiv (quotient-loop-Fin n p)

    quotient-set-Fin : (n : ℕ) → Set l4
    quotient-set-Fin n =
      equivalence-class-Set (R n (raise-Fin-Type-With-Cardinality-ℕ l1 n))

    quotient-map-quotient-Fin :
      (n : ℕ) →
      D n (raise-Fin-Type-With-Cardinality-ℕ l1 n) →
      type-Set (quotient-set-Fin n)
    quotient-map-quotient-Fin n =
      class (R n (raise-Fin-Type-With-Cardinality-ℕ l1 n))

    quotient-reflecting-map-quotient-Fin :
      (n : ℕ) →
      reflecting-map-equivalence-relation
        ( R n (raise-Fin-Type-With-Cardinality-ℕ l1 n))
        ( type-Set (quotient-set-Fin n))
    quotient-reflecting-map-quotient-Fin n =
      quotient-reflecting-map-equivalence-class
        ( R n (raise-Fin-Type-With-Cardinality-ℕ l1 n))

  mere-equiv-D/R-fin-2 :
    (n : ℕ) (X : Type-With-Cardinality-ℕ l1 n) →
    leq-ℕ 2 n → mere-equiv (Fin 2) (equivalence-class (R n X))
  mere-equiv-D/R-fin-2 n X ineq =
    map-trunc-Prop
      ( equiv-D/R-fin-2-equiv n X ineq)
      ( has-cardinality-type-Type-With-Cardinality-ℕ n X)

  map-quotient-delooping-sign :
    (n : ℕ) →
    classifying-type-Type-With-Cardinality-ℕ-Concrete-Group l1 n →
    classifying-type-Type-With-Cardinality-ℕ-Concrete-Group l4 2
  map-quotient-delooping-sign 0 X = raise-Fin-Type-With-Cardinality-ℕ l4 2
  map-quotient-delooping-sign 1 X = raise-Fin-Type-With-Cardinality-ℕ l4 2
  pr1 (map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)) X) =
    equivalence-class (R (succ-ℕ (succ-ℕ n)) X)
  pr2 (map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)) X) =
    mere-equiv-D/R-fin-2 (succ-ℕ (succ-ℕ n)) X star

  quotient-delooping-sign :
    (n : ℕ) →
    hom-Concrete-Group
      ( Type-With-Cardinality-ℕ-Concrete-Group l1 n)
      ( Type-With-Cardinality-ℕ-Concrete-Group l4 2)
  pr1 (quotient-delooping-sign n) = map-quotient-delooping-sign n
  pr2 (quotient-delooping-sign 0) = refl
  pr2 (quotient-delooping-sign 1) = refl
  pr2 (quotient-delooping-sign (succ-ℕ (succ-ℕ n))) =
    eq-pair-Σ
      ( eq-counting-equivalence-class-R n)
      ( eq-is-prop is-prop-type-trunc-Prop)

  map-quotient-delooping-sign-loop :
    ( n : ℕ)
    ( X Y : UU l1) →
    ( eX : mere-equiv (Fin (n +ℕ 2)) X) →
    ( eY : mere-equiv (Fin (n +ℕ 2)) Y) →
    X ＝ Y →
    Id
      ( equivalence-class (R (n +ℕ 2) (X , eX)))
      ( equivalence-class (R (n +ℕ 2) (Y , eY)))
  map-quotient-delooping-sign-loop n X Y eX eY p =
    ap
      ( equivalence-class ∘ R (n +ℕ 2))
      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))

  private
    map-quotient-delooping-sign-loop-Fin :
      ( n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))) →
      type-Group (loop-group-Set (quotient-set-Fin (n +ℕ 2)))
    map-quotient-delooping-sign-loop-Fin n =
      map-quotient-delooping-sign-loop n
        ( raise l1 (Fin (n +ℕ 2)))
        ( raise l1 (Fin (n +ℕ 2)))
        ( unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
        ( unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))

  quotient-delooping-sign-loop :
    ( n : ℕ) →
    hom-Group
      ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
      ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
  pr1 (quotient-delooping-sign-loop n) = map-quotient-delooping-sign-loop-Fin n
  pr2 (quotient-delooping-sign-loop n) {p} {q} =
    ( ap
      ( ap (equivalence-class ∘ R (n +ℕ 2)))
      ( ap
        ( eq-pair-Σ (p ∙ q))
        ( eq-is-prop
          ( is-trunc-Id
            ( is-prop-type-trunc-Prop _
              ( unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))))) ∙
        ( interchange-concat-eq-pair-Σ
          ( p)
          ( q)
          ( eq-is-prop is-prop-type-trunc-Prop)
          ( eq-is-prop is-prop-type-trunc-Prop)))) ∙
      ( ap-concat
        ( equivalence-class ∘ R (n +ℕ 2))
        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))
        ( eq-pair-Σ q (eq-is-prop is-prop-type-trunc-Prop)))

  abstract
    coherence-square-map-quotient-delooping-sign-loop-Set :
      ( n : ℕ)
      ( X Y : UU l1)
      ( eX : mere-equiv (Fin (n +ℕ 2)) X)
      ( eY : mere-equiv (Fin (n +ℕ 2)) Y)
      ( p : X ＝ Y) →
      ( tr (mere-equiv (Fin (n +ℕ 2))) p eX ＝ eY) →
      ( sX : is-set X)
      ( sY : is-set Y) →
      coherence-square-maps
        ( map-equiv
          ( invertible-action-D-equiv
            ( n +ℕ 2)
            ( Y , eY)
            ( X , eX)
            ( map-hom-symmetric-group-loop-group-Set (X , sX) (Y , sY) (p))))
        ( class (R (n +ℕ 2) (Y , eY)))
        ( class (R (n +ℕ 2) (X , eX)))
        ( map-equiv
          ( map-hom-symmetric-group-loop-group-Set
            ( equivalence-class-Set (R (n +ℕ 2) (X , eX)))
            ( equivalence-class-Set (R (n +ℕ 2) (Y , eY)))
            ( map-quotient-delooping-sign-loop n X Y eX eY p)))
    coherence-square-map-quotient-delooping-sign-loop-Set
      n X .X eX .eX refl refl sX sY x =
      ( ap
        ( λ w →
          map-equiv
            ( map-hom-symmetric-group-loop-group-Set
              ( equivalence-class-Set (R (n +ℕ 2) (X , eX)))
              ( equivalence-class-Set (R (n +ℕ 2) (X , eX)))
              ( w))
            ( class (R (n +ℕ 2) (X , eX)) (x)))
        ( ap
          ( λ w → ap (equivalence-class ∘ R (n +ℕ 2)) (eq-pair-eq-fiber w))
          { x = eq-is-prop is-prop-type-trunc-Prop}
          ( eq-is-prop
            ( is-trunc-Id
              ( is-prop-type-trunc-Prop
                ( tr (mere-equiv (Fin (n +ℕ 2))) refl eX)
                ( eX)))))) ∙
      ( ap
        ( class (R (n +ℕ 2) (X , tr (mere-equiv (Fin (n +ℕ 2))) refl eX)))
        ( inv
          ( htpy-eq-equiv
            ( preserves-id-equiv-invertible-action-D-equiv (n +ℕ 2) (X , eX))
            ( x))))

  coherence-square-map-quotient-delooping-sign-loop-Fin :
    (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
    coherence-square-maps
      ( map-quotient-loop-Fin n p)
      ( quotient-map-quotient-Fin (n +ℕ 2))
      ( quotient-map-quotient-Fin (n +ℕ 2))
      ( map-equiv
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-set-Fin (n +ℕ 2))
          ( quotient-set-Fin (n +ℕ 2))
          ( map-quotient-delooping-sign-loop-Fin n p)))
  coherence-square-map-quotient-delooping-sign-loop-Fin n p =
    coherence-square-map-quotient-delooping-sign-loop-Set n
      ( raise l1 (Fin (n +ℕ 2)))
      ( raise l1 (Fin (n +ℕ 2)))
      ( unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
      ( unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
      ( p)
      ( eq-is-prop is-prop-type-trunc-Prop)
      ( is-set-type-Set (raise-Fin-Set l1 (n +ℕ 2)))
      ( is-set-type-Set (raise-Fin-Set l1 (n +ℕ 2)))

  private
    is-contr-equiv-quotient :
      ( n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
      is-contr
        ( Σ ( type-Group (symmetric-Group (quotient-set-Fin (n +ℕ 2))))
            ( λ h' →
              coherence-square-maps
                ( map-quotient-loop-Fin n p)
                ( quotient-map-quotient-Fin (n +ℕ 2))
                ( map-reflecting-map-equivalence-relation
                  ( R ( n +ℕ 2)
                      ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
                  ( quotient-reflecting-map-quotient-Fin (n +ℕ 2)))
                ( map-equiv h')))
    is-contr-equiv-quotient n p =
      unique-equiv-is-set-quotient
        ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
        ( quotient-set-Fin (n +ℕ 2))
        ( quotient-reflecting-map-quotient-Fin (n +ℕ 2))
        ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
        ( quotient-set-Fin (n +ℕ 2))
        ( quotient-reflecting-map-quotient-Fin (n +ℕ 2))
        ( is-set-quotient-equivalence-class
          ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))))
        ( is-set-quotient-equivalence-class
          ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))))
        ( quotient-loop-Fin n p ,
          ( λ {x} {y} →
            preserves-R-invertible-action-D-equiv
              ( n +ℕ 2)
              ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
              ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l1 (n +ℕ 2))
                ( raise-Fin-Set l1 (n +ℕ 2))
                ( p))
              ( x)
              ( y)))

  abstract
    eq-quotient-delooping-sign-loop-equiv-is-set-quotient :
      (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
      Id
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-set-Fin (n +ℕ 2))
          ( quotient-set-Fin (n +ℕ 2))
          ( map-quotient-delooping-sign-loop-Fin n p))
        ( pr1 (center (is-contr-equiv-quotient n p)))
    eq-quotient-delooping-sign-loop-equiv-is-set-quotient n p =
      ap pr1
        { x =
          pair
            ( map-hom-symmetric-group-loop-group-Set
              ( quotient-set-Fin (n +ℕ 2))
              ( quotient-set-Fin (n +ℕ 2))
              ( map-quotient-delooping-sign-loop-Fin n p))
            ( coherence-square-map-quotient-delooping-sign-loop-Fin n p)}
        { y = center (is-contr-equiv-quotient n p)}
        ( eq-is-contr (is-contr-equiv-quotient n p))

  cases-map-quotient-aut-Fin :
    ( n : ℕ) →
    ( h : type-Group (symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))) →
    ( is-decidable
      ( sim-equivalence-relation
        ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
        ( quotient-aut-succ-succ-Fin n h)
        ( map-equiv
          ( invertible-action-D-equiv
            (n +ℕ 2)
            ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
            ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
            ( h))
          ( quotient-aut-succ-succ-Fin n h)))) →
    type-Group (symmetric-Group (quotient-set-Fin (n +ℕ 2)))
  cases-map-quotient-aut-Fin n h (inl D) = id-equiv
  cases-map-quotient-aut-Fin n h (inr ND) =
    that-thing n ∘e (equiv-succ-Fin 2 ∘e (inv-equiv (that-thing n)))

  map-quotient-aut-Fin :
    (n : ℕ) →
    type-Group (symmetric-Group (raise-Fin-Set l1 (n +ℕ 2))) →
    type-Group (symmetric-Group (quotient-set-Fin (n +ℕ 2)))
  map-quotient-aut-Fin n h =
    cases-map-quotient-aut-Fin n h
      ( is-decidable-R
        ( n +ℕ 2)
        ( star)
        ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
        ( quotient-aut-succ-succ-Fin n h)
        ( map-equiv
          ( invertible-action-D-equiv
            (n +ℕ 2)
            ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
            ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
            ( h))
          ( quotient-aut-succ-succ-Fin n h)))

  eq-map-quotient-aut-fin-transposition :
    (n : ℕ) (Y : 2-Element-Decidable-Subtype l1 (raise l1 (Fin (n +ℕ 2)))) →
    Id
      ( map-quotient-aut-Fin n (transposition Y))
      ( that-thing n ∘e (equiv-succ-Fin 2 ∘e (inv-equiv (that-thing n))))
  eq-map-quotient-aut-fin-transposition n Y =
    ap
      ( cases-map-quotient-aut-Fin n (transposition Y))
      { x =
        is-decidable-R
          ( n +ℕ 2)
          ( star)
          ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
          ( quotient-aut-succ-succ-Fin n (transposition Y))
          ( map-equiv
            ( invertible-action-D-equiv
              ( n +ℕ 2)
              ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
              ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
              ( transposition Y))
            ( quotient-aut-succ-succ-Fin n (transposition Y)))}
      { y = inr (not-R-transposition-fin-succ-succ n Y)}
      ( eq-is-prop
        ( is-prop-is-decidable
          ( is-prop-sim-equivalence-relation
            ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
            ( quotient-aut-succ-succ-Fin n (transposition Y))
            ( map-equiv
              ( invertible-action-D-equiv
                ( n +ℕ 2)
                ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
                ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
                ( transposition Y))
              ( quotient-aut-succ-succ-Fin n (transposition Y))))))

  private
    this-third-thing :
      (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
      D ( n +ℕ 2)
        ( raise-Fin l1 (n +ℕ 2) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
    this-third-thing n p =
      quotient-aut-succ-succ-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( p))

  cases-eq-map-quotient-aut-Fin :
    ( n : ℕ)
    ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))))
    ( D : is-decidable
      ( sim-equivalence-relation
        ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
        ( this-third-thing n p)
        ( map-quotient-loop-Fin n p (this-third-thing n p)))) →
    ( k k' : Fin 2) →
    Id
      ( map-inv-equiv
        ( that-thing n)
        ( quotient-map-quotient-Fin (n +ℕ 2) (this-third-thing n p)))
      ( k) →
    Id
      ( map-inv-equiv
        ( that-thing n)
        ( quotient-map-quotient-Fin (n +ℕ 2)
          ( map-quotient-loop-Fin n p (this-third-thing n p))))
      ( k') →
    Id
      ( map-equiv
        ( cases-map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( p))
          ( D))
        ( quotient-map-quotient-Fin (n +ℕ 2) (this-third-thing n p)))
      ( quotient-map-quotient-Fin (n +ℕ 2)
        ( map-quotient-loop-Fin n p (this-third-thing n p)))
  cases-eq-map-quotient-aut-Fin n p (inl D) k k' q r =
    reflects-map-reflecting-map-equivalence-relation
      ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
      ( quotient-reflecting-map-quotient-Fin (n +ℕ 2))
      ( D)
  cases-eq-map-quotient-aut-Fin
    n p (inr ND) (inl (inr star)) (inl (inr star)) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
            ( quotient-set-Fin (n +ℕ 2))
            ( quotient-reflecting-map-quotient-Fin (n +ℕ 2))
            ( is-set-quotient-equivalence-class
              ( R ( n +ℕ 2)
                  ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))))
            ( this-third-thing n p)
            ( map-quotient-loop-Fin n p (this-third-thing n p)))
          ( is-injective-equiv (inv-equiv (that-thing n)) (q ∙ inv r))))
  cases-eq-map-quotient-aut-Fin n p (inr ND) (inl (inr star)) (inr star) q r =
    ( ap
      ( map-equiv (that-thing n))
      ( ap (map-equiv (equiv-succ-Fin 2)) q ∙ inv r)) ∙
    ( ap
      ( λ e →
        map-equiv e
          ( quotient-map-quotient-Fin (n +ℕ 2)
            ( map-quotient-loop-Fin n p (this-third-thing n p)))))
        ( right-inverse-law-equiv (that-thing n))
  cases-eq-map-quotient-aut-Fin n p (inr ND) (inr star) (inl (inr star)) q r =
    ( ap
      ( map-equiv (that-thing n))
      ( ap
        ( map-equiv (equiv-succ-Fin 2))
        ( q) ∙
        ( inv r))) ∙
    ( ap
      ( λ e →
        map-equiv e
          ( quotient-map-quotient-Fin (n +ℕ 2)
            ( map-quotient-loop-Fin n p (this-third-thing n p)))))
    ( right-inverse-law-equiv (that-thing n))
  cases-eq-map-quotient-aut-Fin n p (inr ND) (inr star) (inr star) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
            ( quotient-set-Fin (n +ℕ 2))
            ( quotient-reflecting-map-quotient-Fin (n +ℕ 2))
            ( is-set-quotient-equivalence-class
              ( R ( n +ℕ 2)
                  ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))))
            ( this-third-thing n p)
            ( map-quotient-loop-Fin n p (this-third-thing n p)))
          ( is-injective-equiv (inv-equiv (that-thing n)) (q ∙ inv r))))

  eq-map-quotient-aut-Fin :
    (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
    Id
      ( map-equiv
        ( map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( p)))
        ( quotient-map-quotient-Fin (n +ℕ 2) (this-third-thing n p)))
      ( quotient-map-quotient-Fin (n +ℕ 2)
        ( map-quotient-loop-Fin n p (this-third-thing n p)))
  eq-map-quotient-aut-Fin n p =
    cases-eq-map-quotient-aut-Fin n p
      ( is-decidable-R (n +ℕ 2) star
        ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
        ( this-third-thing n p)
        ( map-quotient-loop-Fin n p (this-third-thing n p)))
        ( map-inv-equiv
          ( that-thing n)
          ( quotient-map-quotient-Fin (n +ℕ 2) (this-third-thing n p)))
        ( map-inv-equiv
          ( that-thing n)
          ( quotient-map-quotient-Fin (n +ℕ 2)
            ( map-quotient-loop-Fin n p (this-third-thing n p))))
        ( refl)
        ( refl)

  eq-map-quotient-aut-loop-equiv-is-set-quotient :
    (n : ℕ) (p : type-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))) →
    Id
      ( map-quotient-aut-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( p)))
      ( pr1 (center (is-contr-equiv-quotient n p)))
  eq-map-quotient-aut-loop-equiv-is-set-quotient n p =
    eq-equiv-eq-one-value-equiv-is-set-quotient
      ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2)))
      ( quotient-set-Fin (n +ℕ 2))
      ( quotient-reflecting-map-quotient-Fin (n +ℕ 2))
      ( is-set-quotient-equivalence-class
        ( R (n +ℕ 2) (raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))))
      ( inv-equiv (that-thing n))
      ( map-quotient-loop-Fin n p)
      ( λ {x} {y} →
        preserves-R-invertible-action-D-equiv
          ( n +ℕ 2)
          ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
          ( raise-Fin-Type-With-Cardinality-ℕ l1 (n +ℕ 2))
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( p))
          ( x)
          ( y))
      ( map-equiv
        ( map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( p))))
      ( this-third-thing n p)
      ( eq-map-quotient-aut-Fin n p)
      ( is-equiv-map-equiv (quotient-loop-Fin n p))
      ( is-equiv-map-equiv
        ( map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( raise-Fin-Set l1 (n +ℕ 2))
            ( p))))

  eq-quotient-delooping-sign-loop-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( quotient-delooping-sign-loop n)
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
          ( comp-hom-Group
            ( symmetric-Group (Fin-Set 2))
            ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
            ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
            ( hom-inv-symmetric-group-loop-group-Set
              ( quotient-set-Fin (n +ℕ 2)))
            ( hom-symmetric-group-equiv-Set
              ( Fin-Set 2)
              ( quotient-set-Fin (n +ℕ 2))
              ( that-thing n)))
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( compute-raise-Fin l1 (n +ℕ 2))))
  eq-quotient-delooping-sign-loop-sign-homomorphism n =
    map-inv-equiv
      ( equiv-ap-emb
        ( restriction-generating-subset-Group
          ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
          ( is-transposition-permutation-Prop {l2 = l1})
          ( tr
            ( λ s →
              is-generating-set-Group
                ( symmetric-Group (raise l1 (Fin (n +ℕ 2)) , s))
                ( is-transposition-permutation-Prop))
            ( eq-is-prop (is-prop-is-set (raise l1 (Fin (n +ℕ 2)))))
            ( is-generated-transposition-symmetric-Fin-Level
              ( n +ℕ 2)
              ( raise l1 (Fin (n +ℕ 2)) ,
                unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))))
          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))))
      ( eq-htpy
        ( λ (f , s) →
          apply-universal-property-trunc-Prop s
            ( Id-Prop (set-Group (loop-group-Set (quotient-set-Fin (n +ℕ 2))))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-set-Group
                        ( symmetric-Group (raise l1 (Fin (n +ℕ 2)) , s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l1 (Fin (n +ℕ 2)))))
                    ( is-generated-transposition-symmetric-Fin-Level
                      ( n +ℕ 2)
                      ( raise l1 (Fin (n +ℕ 2)) ,
                        unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))))
                  ( loop-group-Set (quotient-set-Fin (n +ℕ 2))))
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                  ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
                  ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                  ( quotient-delooping-sign-loop n)
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l1 (n +ℕ 2))))
                ( f , s))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-set-Group
                        ( symmetric-Group (raise l1 (Fin (n +ℕ 2)) , s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l1 (Fin (n +ℕ 2)))))
                    ( is-generated-transposition-symmetric-Fin-Level
                      ( n +ℕ 2)
                      ( raise l1 (Fin (n +ℕ 2)) ,
                        unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))))
                    ( loop-group-Set (quotient-set-Fin (n +ℕ 2))))
                  ( comp-hom-Group
                    ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                    ( symmetric-Group (Fin-Set (n +ℕ 2)))
                    ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                    ( comp-hom-Group
                      ( symmetric-Group (Fin-Set (n +ℕ 2)))
                      ( symmetric-Group (Fin-Set 2))
                      ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                      ( comp-hom-Group
                        ( symmetric-Group (Fin-Set 2))
                        ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                        ( hom-inv-symmetric-group-loop-group-Set
                          ( quotient-set-Fin (n +ℕ 2)))
                        ( hom-symmetric-group-equiv-Set
                          ( Fin-Set 2)
                          ( quotient-set-Fin (n +ℕ 2))
                          ( that-thing n)))
                      ( sign-homomorphism (n +ℕ 2)
                        ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
                    ( hom-inv-symmetric-group-equiv-Set
                      ( Fin-Set (n +ℕ 2))
                      ( raise-Fin-Set l1 (n +ℕ 2))
                      ( compute-raise-Fin l1 (n +ℕ 2))))
                ( f , s)))
            λ (Y , q) →
            ( eq-map-restriction-generating-subset-Group
              ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
              ( is-transposition-permutation-Prop)
              ( tr
                ( λ s₁ →
                  is-generating-set-Group
                    ( symmetric-Group (raise l1 (Fin (n +ℕ 2)) , s₁))
                    ( is-transposition-permutation-Prop))
                ( eq-is-prop (is-prop-is-set (raise l1 (Fin (n +ℕ 2)))))
                ( is-generated-transposition-symmetric-Fin-Level
                  ( n +ℕ 2)
                  ( raise l1 (Fin (n +ℕ 2)) ,
                    unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))))
              ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
              ( comp-hom-Group
                ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
                ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                ( quotient-delooping-sign-loop n)
                ( hom-inv-symmetric-group-loop-group-Set
                  ( raise-Fin-Set l1 (n +ℕ 2))))
              ( f , s)) ∙
            ( htpy-eq-hom-Group
              ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
              ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
              ( id-hom-Group (loop-group-Set (quotient-set-Fin (n +ℕ 2))))
              ( comp-hom-Group
                ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                ( hom-inv-symmetric-group-loop-group-Set
                  ( quotient-set-Fin (n +ℕ 2)))
                ( hom-symmetric-group-loop-group-Set
                  ( quotient-set-Fin (n +ℕ 2))))
              ( inv
                ( is-retraction-hom-inv-symmetric-group-loop-group-Set
                  ( quotient-set-Fin (n +ℕ 2))))
              ( ap
                ( equivalence-class ∘ R (n +ℕ 2))
                ( eq-pair-Σ
                  ( inv (eq-equiv f))
                  ( eq-is-prop is-prop-type-trunc-Prop))) ∙
              ( ap
                ( map-hom-Group
                  ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                  ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( quotient-set-Fin (n +ℕ 2))))
                ( eq-quotient-delooping-sign-loop-equiv-is-set-quotient n
                  ( inv (eq-equiv f)) ∙
                  ( inv
                    ( eq-map-quotient-aut-loop-equiv-is-set-quotient n
                      ( inv (eq-equiv f))))) ∙
                ( ap
                  ( λ g →
                    map-hom-Group
                      ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                      ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                      ( hom-inv-symmetric-group-loop-group-Set
                        ( quotient-set-Fin (n +ℕ 2)))
                      ( map-quotient-aut-Fin n g))
                  ( commutative-inv-map-hom-symmetric-group-loop-group-Set
                    ( raise l1 (Fin (n +ℕ 2)))
                    ( raise l1 (Fin (n +ℕ 2)))
                    ( eq-equiv f)
                    ( pr2 (raise-Fin-Set l1 (n +ℕ 2)))
                    ( pr2 (raise-Fin-Set l1 (n +ℕ 2))) ∙
                    ( ap inv-equiv
                      ( ap
                        ( map-hom-symmetric-group-loop-group-Set
                          ( raise-Fin-Set l1 (n +ℕ 2))
                          ( raise-Fin-Set l1 (n +ℕ 2)))
                        ( ap
                          ( eq-equiv)
                          ( inv (inv-inv-equiv f)) ∙
                          ( inv
                            ( commutativity-inv-eq-equiv (inv-equiv f)))) ∙
                        ( htpy-eq-hom-Group
                          ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                          ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                          ( comp-hom-Group
                            ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                            ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
                            ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                            ( hom-symmetric-group-loop-group-Set
                              ( raise-Fin-Set l1 (n +ℕ 2)))
                            ( hom-inv-symmetric-group-loop-group-Set
                              ( raise-Fin-Set l1 (n +ℕ 2))))
                          ( id-hom-Group
                            ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2))))
                          ( is-section-hom-inv-symmetric-group-loop-group-Set
                            ( raise-Fin-Set l1 (n +ℕ 2)))
                          ( inv-equiv f) ∙
                          ( ap inv-equiv (inv q) ∙
                            ( own-inverse-is-involution
                              ( is-involution-map-transposition Y))))))) ∙
                  ( ap
                    ( map-hom-Group
                      ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                      ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                      ( hom-inv-symmetric-group-loop-group-Set
                        ( quotient-set-Fin (n +ℕ 2))))
                    ( ap
                      ( map-quotient-aut-Fin n)
                      ( own-inverse-is-involution
                        ( is-involution-map-transposition Y)) ∙
                      ( eq-map-quotient-aut-fin-transposition n Y ∙
                        ( ap
                          ( λ e →
                            (that-thing n) ∘e (e ∘e inv-equiv ( that-thing n)))
                          ( inv
                            ( eq-sign-homomorphism-transposition
                              ( n +ℕ 2)
                              ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)
                              ( map-equiv
                                ( equiv-universes-2-Element-Decidable-Subtype
                                  ( Fin (n +ℕ 2))
                                  ( l1)
                                  ( lzero))
                                ( transposition-conjugation-equiv {l4 = l1}
                                  ( raise l1 (Fin (n +ℕ 2)))
                                  ( Fin (n +ℕ 2))
                                  ( inv-equiv (compute-raise-Fin l1 (n +ℕ 2)))
                                  ( Y)))) ∙
                            ( ap
                              ( map-hom-Group
                                ( symmetric-Group
                                  ( set-Type-With-Cardinality-ℕ (n +ℕ 2)
                                    ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
                                ( symmetric-Group (Fin-Set 2))
                                ( sign-homomorphism
                                  ( n +ℕ 2)
                                  ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
                              ( inv
                                ( eq-equiv-universes-transposition
                                  ( Fin (n +ℕ 2))
                                  ( l1)
                                  ( lzero)
                                  ( transposition-conjugation-equiv
                                    ( raise l1 (Fin (n +ℕ 2)))
                                    ( Fin (n +ℕ 2))
                                    ( inv-equiv (compute-raise-Fin l1 (n +ℕ 2)))
                                    ( Y))) ∙
                                ( eq-htpy-equiv
                                  ( correct-transposition-conjugation-equiv
                                    ( raise l1 (Fin (n +ℕ 2)))
                                    ( Fin (n +ℕ 2))
                                    ( inv-equiv (compute-raise-Fin l1 (n +ℕ 2)))
                                    ( Y)) ∙
                                  ( associative-comp-equiv
                                    ( inv-equiv
                                      ( inv-equiv
                                        ( compute-raise-Fin l1 (n +ℕ 2))))
                                    ( transposition Y)
                                    ( inv-equiv
                                      ( compute-raise-Fin l1 (n +ℕ 2))) ∙
                                    ( ap
                                      ( λ e →
                                        ( inv-equiv
                                          ( compute-raise-Fin l1 (n +ℕ 2))) ∘e
                                        ( transposition Y ∘e e))
                                      ( inv-inv-equiv
                                        ( compute-raise-Fin l1 (n +ℕ 2))) ∙
                                      ( ap
                                        ( λ e →
                                          ( inv-equiv
                                            ( compute-raise-Fin l1 (n +ℕ 2))) ∘e
                                          ( e ∘e compute-raise-Fin l1 (n +ℕ 2)))
                                        ( q))))))))))) ∙
                    ( inv
                      ( eq-map-restriction-generating-subset-Group
                        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                        ( is-transposition-permutation-Prop)
                        ( tr
                          ( λ s →
                            is-generating-set-Group
                              ( symmetric-Group (raise l1 (Fin (n +ℕ 2)) , s))
                              ( is-transposition-permutation-Prop))
                          ( eq-is-prop
                            ( is-prop-is-set (raise l1 (Fin (n +ℕ 2)))))
                          ( is-generated-transposition-symmetric-Fin-Level
                            ( n +ℕ 2)
                            ( raise l1 (Fin (n +ℕ 2)) ,
                              unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))))
                        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                        ( comp-hom-Group
                          ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                          ( symmetric-Group (Fin-Set (n +ℕ 2)))
                          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                          ( comp-hom-Group
                            ( symmetric-Group (Fin-Set (n +ℕ 2)))
                            ( symmetric-Group (Fin-Set 2))
                            ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                            ( comp-hom-Group
                              ( symmetric-Group (Fin-Set 2))
                              ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                              ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                              ( hom-inv-symmetric-group-loop-group-Set
                                ( quotient-set-Fin (n +ℕ 2)))
                              ( hom-symmetric-group-equiv-Set
                                ( Fin-Set 2)
                                ( quotient-set-Fin (n +ℕ 2))
                                ( that-thing n)))
                            ( sign-homomorphism
                              ( n +ℕ 2)
                              ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
                          ( hom-inv-symmetric-group-equiv-Set
                            ( Fin-Set (n +ℕ 2))
                            ( raise-Fin-Set l1 (n +ℕ 2))
                            ( compute-raise-Fin l1 (n +ℕ 2))))
                        ( f , s)))))))))

  eq-quotient-delooping-loop-Type-With-Cardinality-ℕ-Group :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group l4 2)
        ( hom-iso-Group
          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
          ( Type-With-Cardinality-ℕ-Group l4 2)
          ( comp-iso-Group
            ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
            ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
            ( Type-With-Cardinality-ℕ-Group l4 2)
            ( inv-iso-Group
              ( Type-With-Cardinality-ℕ-Group l4 2)
              ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
              ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l4 2))
            ( iso-loop-group-equiv-Set
              ( quotient-set-Fin (n +ℕ 2))
              ( raise-Set l4 (Fin-Set 2))
              ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n)))))
        ( quotient-delooping-sign-loop n))
      ( comp-hom-Group
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
        ( Type-With-Cardinality-ℕ-Group l4 2)
        ( hom-group-hom-Concrete-Group
          ( Type-With-Cardinality-ℕ-Concrete-Group l1 (n +ℕ 2))
          ( Type-With-Cardinality-ℕ-Concrete-Group l4 2)
          ( quotient-delooping-sign (n +ℕ 2)))
        ( hom-iso-Group
          ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
          ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
          ( inv-iso-Group
            ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
            ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
            ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2)))))
  eq-quotient-delooping-loop-Type-With-Cardinality-ℕ-Group n =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ap
            ( λ r → eq-pair-Σ r (eq-is-prop is-prop-type-trunc-Prop))
            ( ap inv
              ( inv
                ( compute-eq-equiv-comp-equiv
                  ( equiv-eq
                    ( inv
                      ( ap
                        ( equivalence-class ∘ R (n +ℕ 2))
                        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))) ∘e
                    ( inv-equiv
                      ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n))))
                  ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n))) ∙
                ( right-whisker-concat
                  ( inv
                    ( compute-eq-equiv-comp-equiv
                      ( inv-equiv
                        ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n)))
                      ( equiv-eq
                        ( inv
                          ( ap
                            ( equivalence-class ∘ R (n +ℕ 2))
                            ( eq-pair-Σ p
                              ( eq-is-prop is-prop-type-trunc-Prop)))))) ∙
                    ( right-whisker-concat
                      ( inv
                        ( commutativity-inv-eq-equiv
                          ( compute-raise-Fin l4 2 ∘e
                            inv-equiv (that-thing n))))
                      ( eq-equiv
                        ( equiv-eq
                          ( inv
                            ( ap
                              ( equivalence-class ∘ R (n +ℕ 2))
                              ( eq-pair-Σ p
                                ( eq-is-prop is-prop-type-trunc-Prop)))))) ∙
                      ( ap
                        ( λ e →
                          inv (eq-counting-equivalence-class-R n) ∙
                            ( map-equiv e
                              ( inv
                                ( ap
                                  ( equivalence-class ∘ R (n +ℕ 2))
                                  ( eq-pair-Σ p
                                    ( eq-is-prop is-prop-type-trunc-Prop))))))
                        ( left-inverse-law-equiv equiv-univalence))))
                  ( eq-counting-equivalence-class-R n))) ∙
              ( distributive-inv-concat
                ( inv (eq-counting-equivalence-class-R n) ∙
                  ( inv
                    ( ap
                      ( equivalence-class ∘ R (n +ℕ 2))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))
                ( eq-counting-equivalence-class-R n) ∙
                ( left-whisker-concat
                  ( inv (eq-counting-equivalence-class-R n))
                  ( distributive-inv-concat
                    ( inv (eq-counting-equivalence-class-R n))
                    ( inv
                      ( ap
                        ( equivalence-class ∘ R (n +ℕ 2))
                        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))) ∙
                    ( right-whisker-concat
                      ( inv-inv
                        ( ap
                          ( equivalence-class ∘ R (n +ℕ 2))
                          ( eq-pair-Σ p
                            ( eq-is-prop is-prop-type-trunc-Prop))))
                      ( inv (inv (eq-counting-equivalence-class-R n))) ∙
                      ( left-whisker-concat
                        ( ap
                          ( equivalence-class ∘ R (n +ℕ 2))
                          ( eq-pair-Σ p
                            ( eq-is-prop is-prop-type-trunc-Prop)))
                        ( inv-inv (eq-counting-equivalence-class-R n)))))))) ∙
            ( ( ap
              ( eq-pair-Σ
                ( inv (eq-counting-equivalence-class-R n) ∙
                  ( ap
                    ( equivalence-class ∘ R (n +ℕ 2))
                    ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)) ∙
                    ( eq-counting-equivalence-class-R n))))
              ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _))) ∙
              ( interchange-concat-eq-pair-Σ
                ( inv (eq-counting-equivalence-class-R n))
                ( ap
                  ( equivalence-class ∘ R (n +ℕ 2))
                  ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)) ∙
                  ( eq-counting-equivalence-class-R n))
                ( eq-is-prop is-prop-type-trunc-Prop)
                ( _) ∙
                ( left-whisker-concat
                  ( eq-pair-Σ
                    ( inv (eq-counting-equivalence-class-R n))
                    ( eq-is-prop is-prop-type-trunc-Prop))
                  ( interchange-concat-eq-pair-Σ
                    ( ap
                      ( equivalence-class ∘ R (n +ℕ 2))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))
                    ( eq-counting-equivalence-class-R n)
                    ( eq-is-prop is-prop-type-trunc-Prop)
                    ( eq-is-prop is-prop-type-trunc-Prop) ∙
                    ( right-whisker-concat
                      ( ap
                        ( λ w → eq-pair-Σ (pr1 w) (pr2 w))
                        { y =
                          pair-eq-Σ
                            ( ap
                              ( map-quotient-delooping-sign (n +ℕ 2))
                              ( eq-pair-Σ p
                                ( eq-is-prop is-prop-type-trunc-Prop)))}
                        ( eq-pair-Σ
                          ( inv
                            ( pr1-pair-eq-Σ-ap _
                              ( eq-pair-Σ p
                                ( eq-is-prop is-prop-type-trunc-Prop))))
                          ( eq-is-prop
                            ( is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
                          is-section-pair-eq-Σ
                          ( map-quotient-delooping-sign
                            ( n +ℕ 2)
                            ( raise-Fin-Type-With-Cardinality-ℕ
                              ( l1)
                              ( n +ℕ 2)))
                          ( map-quotient-delooping-sign
                            ( n +ℕ 2)
                            ( raise-Fin-Type-With-Cardinality-ℕ
                              ( l1)
                              ( n +ℕ 2)))
                          ( ap
                            ( map-quotient-delooping-sign (n +ℕ 2))
                            ( eq-pair-Σ p
                              ( eq-is-prop is-prop-type-trunc-Prop))))
                      ( eq-pair-Σ
                        ( eq-equiv
                          ( compute-raise-Fin l4 2 ∘e
                            inv-equiv (that-thing n)))
                        ( eq-is-prop is-prop-type-trunc-Prop))))))) ∙
              ( right-whisker-concat
                ( ap
                  ( eq-pair-Σ (inv (eq-counting-equivalence-class-R n)))
                  ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _))) ∙
                  ( inv
                    ( distributive-inv-eq-pair-Σ
                      ( eq-counting-equivalence-class-R n)
                      ( eq-is-prop is-prop-type-trunc-Prop))))
                ( ( ap
                    ( map-quotient-delooping-sign (n +ℕ 2))
                    ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                  ( eq-pair-Σ
                    ( eq-counting-equivalence-class-R n)
                    ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                ( inv
                  ( eq-tr-type-Ω
                    ( eq-pair-Σ
                      ( eq-counting-equivalence-class-R n)
                      ( eq-is-prop is-prop-type-trunc-Prop))
                    ( ap (map-quotient-delooping-sign (n +ℕ 2))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))))
          ( semigroup-Group
            ( Type-With-Cardinality-ℕ-Group l4 2))
          ( pr1
            ( comp-hom-Group
              ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
              ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
              ( Type-With-Cardinality-ℕ-Group l4 2)
              ( hom-group-hom-Concrete-Group
                ( Type-With-Cardinality-ℕ-Concrete-Group l1 (n +ℕ 2))
                ( Type-With-Cardinality-ℕ-Concrete-Group l4 2)
                ( quotient-delooping-sign (n +ℕ 2)))
              ( hom-iso-Group
                ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
                ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
                ( inv-iso-Group
                  ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
                  ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
                  ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l1
                    ( n +ℕ 2))))))))

  symmetric-abstract-type-with-cardinality-ℕ-group-quotient-hom :
    (n : ℕ) →
    hom-Group
      ( symmetric-Group (Fin-Set 2))
      ( Type-With-Cardinality-ℕ-Group l4 2)
  symmetric-abstract-type-with-cardinality-ℕ-group-quotient-hom n =
    comp-hom-Group
      ( symmetric-Group (Fin-Set 2))
      ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
      ( Type-With-Cardinality-ℕ-Group l4 2)
      ( comp-hom-Group
        ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group l4 2)
        ( hom-iso-Group
          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
          ( Type-With-Cardinality-ℕ-Group l4 2)
          ( comp-iso-Group
            ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
            ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
            ( Type-With-Cardinality-ℕ-Group l4 2)
            ( inv-iso-Group
              ( Type-With-Cardinality-ℕ-Group l4 2)
              ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
              ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l4 2))
            ( iso-loop-group-equiv-Set
              ( quotient-set-Fin (n +ℕ 2))
              ( raise-Set l4 (Fin-Set 2))
              ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n)))))
        ( hom-inv-symmetric-group-loop-group-Set (quotient-set-Fin (n +ℕ 2))))
      ( hom-symmetric-group-equiv-Set
        ( Fin-Set 2)
        ( quotient-set-Fin (n +ℕ 2))
        ( that-thing n))

  eq-quotient-delooping-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group l4 2)
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
          ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
          ( Type-With-Cardinality-ℕ-Group l4 2)
          ( hom-group-hom-Concrete-Group
            ( Type-With-Cardinality-ℕ-Concrete-Group l1 (n +ℕ 2))
            ( Type-With-Cardinality-ℕ-Concrete-Group l4 2)
            ( quotient-delooping-sign (n +ℕ 2)))
          ( hom-inv-iso-Group
            ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
            ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
            ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))))
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group l4 2)
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( Type-With-Cardinality-ℕ-Group l4 2)
          ( symmetric-abstract-type-with-cardinality-ℕ-group-quotient-hom
            ( n))
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( compute-raise-Fin l1 (n +ℕ 2))))
  eq-quotient-delooping-sign-homomorphism n =
    ( ap
      ( λ f →
        comp-hom-Group
          ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
          ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
          ( Type-With-Cardinality-ℕ-Group l4 2)
          ( f)
          ( hom-inv-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (n +ℕ 2))))
      ( inv
        ( eq-quotient-delooping-loop-Type-With-Cardinality-ℕ-Group n))) ∙
    ( associative-comp-hom-Group
      ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
      ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
      ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
      ( Type-With-Cardinality-ℕ-Group l4 2)
      ( hom-iso-Group
        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group l4 2)
        ( comp-iso-Group
          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
          ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
          ( Type-With-Cardinality-ℕ-Group l4 2)
          ( inv-iso-Group
            ( Type-With-Cardinality-ℕ-Group l4 2)
            ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
            ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l4 2))
          ( iso-loop-group-equiv-Set
            ( quotient-set-Fin (n +ℕ 2))
            ( raise-Set l4 (Fin-Set 2))
            ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n)))))
      ( quotient-delooping-sign-loop n)
      ( hom-inv-symmetric-group-loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))) ∙
      ( ap
        ( comp-hom-Group
            ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
            ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
            ( Type-With-Cardinality-ℕ-Group l4 2)
            ( hom-iso-Group
              ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
              ( Type-With-Cardinality-ℕ-Group l4 2)
              ( comp-iso-Group
                ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
                ( Type-With-Cardinality-ℕ-Group l4 2)
                ( inv-iso-Group
                  ( Type-With-Cardinality-ℕ-Group l4 2)
                  ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
                  ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l4 2))
                ( iso-loop-group-equiv-Set
                  ( quotient-set-Fin (n +ℕ 2))
                  ( raise-Set l4 (Fin-Set 2))
                  ( compute-raise-Fin l4 2 ∘e inv-equiv (that-thing n))))))
        ( eq-quotient-delooping-sign-loop-sign-homomorphism n) ∙
        ( eq-pair-eq-fiber
          ( eq-is-prop
            ( is-prop-preserves-mul-Semigroup
              ( semigroup-Group (symmetric-Group (raise-Fin-Set l1 (n +ℕ 2))))
              ( semigroup-Group
                ( Type-With-Cardinality-ℕ-Group l4 2))
              ( pr1
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
                  ( symmetric-Group (Fin-Set (n +ℕ 2)))
                  ( Type-With-Cardinality-ℕ-Group l4 2)
                  ( comp-hom-Group
                    ( symmetric-Group (Fin-Set (n +ℕ 2)))
                    ( symmetric-Group (Fin-Set 2))
                    ( Type-With-Cardinality-ℕ-Group l4 2)
                    ( comp-hom-Group
                      ( symmetric-Group (Fin-Set 2))
                      ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                      ( Type-With-Cardinality-ℕ-Group l4 2)
                      ( comp-hom-Group
                        ( symmetric-Group (quotient-set-Fin (n +ℕ 2)))
                        ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                        ( Type-With-Cardinality-ℕ-Group l4 2)
                        ( hom-iso-Group
                          ( loop-group-Set (quotient-set-Fin (n +ℕ 2)))
                          ( Type-With-Cardinality-ℕ-Group l4 2)
                          ( comp-iso-Group
                            ( loop-group-Set ( quotient-set-Fin (n +ℕ 2)))
                            ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
                            ( Type-With-Cardinality-ℕ-Group l4 2)
                            ( inv-iso-Group
                              ( Type-With-Cardinality-ℕ-Group l4 2)
                              ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
                              ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group
                                ( l4)
                                ( 2)))
                            ( iso-loop-group-equiv-Set
                              ( quotient-set-Fin (n +ℕ 2))
                              ( raise-Set l4 (Fin-Set 2))
                              ( compute-raise-Fin l4 2 ∘e
                                inv-equiv (that-thing n)))))
                        ( hom-inv-symmetric-group-loop-group-Set
                          ( quotient-set-Fin (n +ℕ 2))))
                      ( hom-symmetric-group-equiv-Set
                        ( Fin-Set 2)
                        ( quotient-set-Fin (n +ℕ 2))
                        ( that-thing n)))
                    ( sign-homomorphism
                      ( n +ℕ 2)
                      ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
                  ( hom-inv-symmetric-group-equiv-Set (Fin-Set (n +ℕ 2))
                    ( raise-Fin-Set l1 (n +ℕ 2))
                    ( compute-raise-Fin l1 (n +ℕ 2))))))))))
```

### General case for the construction of the delooping of sign homomorphism (Proposition 22)

```agda
module _
  { l1 l2 : Level}
  ( Q :
    (n : ℕ) →
    Type-With-Cardinality-ℕ l1 n → Type-With-Cardinality-ℕ l2 2)
  ( equiv-Q-fin-fin-2 :
    (n : ℕ) →
    leq-ℕ 2 n →
    Fin 2 ≃
    ( type-Type-With-Cardinality-ℕ 2
      ( Q n (raise l1 (Fin n) , unit-trunc-Prop (compute-raise-Fin l1 n)))))
  ( Q-transposition-swap : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l1 (raise-Fin l1 (n +ℕ 2))) →
    ( x : type-Type-With-Cardinality-ℕ 2
      ( Q ( n +ℕ 2)
          ( raise l1 (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2))))) →
    ( x) ≠
    ( map-equiv
      ( action-equiv-family-over-subuniverse
        ( mere-equiv-Prop (Fin (n +ℕ 2)))
        ( type-Type-With-Cardinality-ℕ 2 ∘ Q (n +ℕ 2))
        ( raise l1 (Fin (n +ℕ 2)) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
        ( raise l1 (Fin (n +ℕ 2)) ,
          unit-trunc-Prop (compute-raise-Fin l1 (n +ℕ 2)))
        ( transposition Y))
      ( x)))
  where

  private
    equiv-Q-equivalence-class :
      (n : ℕ) (X : Type-With-Cardinality-ℕ l1 n) →
      type-Type-With-Cardinality-ℕ 2 (Q n X) ≃
      equivalence-class
        ( Id-equivalence-relation (set-Type-With-Cardinality-ℕ 2 (Q n X)))
    equiv-Q-equivalence-class n X =
      equiv-uniqueness-set-quotient
        ( Id-equivalence-relation (set-Type-With-Cardinality-ℕ 2 (Q n X)))
        ( set-Type-With-Cardinality-ℕ 2 (Q n X))
        ( id-reflecting-map-Id-equivalence-relation
          ( set-Type-With-Cardinality-ℕ 2 (Q n X)))
        ( is-set-quotient-id-Id-equivalence-relation
          ( set-Type-With-Cardinality-ℕ 2 (Q n X)))
        ( equivalence-class-Set
          ( Id-equivalence-relation
            ( set-Type-With-Cardinality-ℕ 2 (Q n X))))
        ( quotient-reflecting-map-equivalence-class
          ( Id-equivalence-relation
            ( set-Type-With-Cardinality-ℕ 2 (Q n X))))
        ( is-set-quotient-equivalence-class
          ( Id-equivalence-relation
            ( set-Type-With-Cardinality-ℕ 2 (Q n X))))

    equiv-fin-2-equivalence-class :
      (n : ℕ) (X : Type-With-Cardinality-ℕ l1 n) → leq-ℕ 2 n →
      Fin n ≃ type-Type-With-Cardinality-ℕ n X →
      Fin 2 ≃
      equivalence-class
        ( Id-equivalence-relation (set-Type-With-Cardinality-ℕ 2 (Q n X)))
    equiv-fin-2-equivalence-class n X H h =
      tr
        ( λ Y →
          Fin 2 ≃
          equivalence-class
            ( Id-equivalence-relation
              ( set-Type-With-Cardinality-ℕ 2 (Q n Y))))
        ( eq-pair-Σ
          ( eq-equiv (h ∘e inv-equiv (compute-raise-Fin l1 n)))
          ( eq-is-prop is-prop-type-trunc-Prop))
        ( equiv-Q-equivalence-class n
          ( raise l1 (Fin n) ,
            unit-trunc-Prop (compute-raise-Fin l1 n)) ∘e equiv-Q-fin-fin-2 n H)

  delooping-sign :
    (n : ℕ) →
    hom-Concrete-Group
      ( Type-With-Cardinality-ℕ-Concrete-Group l1 n)
      ( Type-With-Cardinality-ℕ-Concrete-Group (lsuc l2) 2)
  delooping-sign =
    quotient-delooping-sign
      ( λ n X → type-Type-With-Cardinality-ℕ 2 (Q n X))
      ( λ n X →
        Id-equivalence-relation (set-Type-With-Cardinality-ℕ 2 (Q n X)))
      ( λ n _ X → has-decidable-equality-has-cardinality-ℕ 2 (pr2 (Q n X)))
      ( equiv-fin-2-equivalence-class)
      ( λ n _ → map-equiv (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1))
      ( λ n Y →
        Q-transposition-swap n Y
          ( pr1 (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1)))

  eq-delooping-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group (lsuc l2) 2)
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
          ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
          ( Type-With-Cardinality-ℕ-Group (lsuc l2) 2)
          ( hom-group-hom-Concrete-Group
            ( Type-With-Cardinality-ℕ-Concrete-Group l1 (n +ℕ 2))
            ( Type-With-Cardinality-ℕ-Concrete-Group (lsuc l2) 2)
            ( delooping-sign (n +ℕ 2)))
          ( hom-inv-iso-Group
            ( Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))
            ( loop-group-Set (raise-Fin-Set l1 (n +ℕ 2)))
            ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l1 (n +ℕ 2))))
        ( hom-inv-symmetric-group-loop-group-Set (raise-Fin-Set l1 (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group (lsuc l2) 2)
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( Type-With-Cardinality-ℕ-Group (lsuc l2) 2)
          ( symmetric-abstract-type-with-cardinality-ℕ-group-quotient-hom
            ( λ n X → type-Type-With-Cardinality-ℕ 2 (Q n X))
            ( λ n X →
              Id-equivalence-relation
                ( set-Type-With-Cardinality-ℕ 2 (Q n X)))
            ( λ n _ X →
              has-decidable-equality-has-cardinality-ℕ 2 (pr2 (Q n X)))
            ( equiv-fin-2-equivalence-class)
            ( λ n _ → pr1 (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1))
            ( λ n Y →
              Q-transposition-swap n Y
                ( pr1 (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1)))
            ( n))
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l1 (n +ℕ 2))
          ( compute-raise-Fin l1 (n +ℕ 2))))
  eq-delooping-sign-homomorphism =
    eq-quotient-delooping-sign-homomorphism
      ( λ n X → type-Type-With-Cardinality-ℕ 2 (Q n X))
      ( λ n X →
        Id-equivalence-relation (set-Type-With-Cardinality-ℕ 2 (Q n X)))
      ( λ n _ X → has-decidable-equality-has-cardinality-ℕ 2 (pr2 (Q n X)))
      ( equiv-fin-2-equivalence-class)
      ( λ n _ → pr1 (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1))
      ( λ n Y →
        Q-transposition-swap n Y
          ( pr1 (equiv-Q-fin-fin-2 (n +ℕ 2) star) (zero-Fin 1)))
```

## See also

- Definition of the delooping of the sign homomorphism based on Cartier
  [`finite-group-theory.cartier-delooping-sign-homomorphism`](finite-group-theory.cartier-delooping-sign-homomorphism.md).
- Definition of the delooping of the sign homomorphism based on Simpson
  [`finite-group-theory.simpson-delooping-sign-homomorphism`](finite-group-theory.simpson-delooping-sign-homomorphism.md).

## References

{{#bibliography}} {{#reference MR23}}
