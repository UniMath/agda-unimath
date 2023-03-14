# Deloopings of the sign homomorphism

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module finite-group-theory.delooping-sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-type-groups
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

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
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.truncated-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-generated-subgroups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.subgroups-generated-by-subsets-groups
open import group-theory.symmetric-groups

open import synthetic-homotopy-theory.loop-spaces

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.set-quotients-of-index-two
open import univalent-combinatorics.standard-finite-types
```

</details>

### Deloopings of the sign homomorphism

```agda
module _
  { l1 l2 l3 : Level}
  ( D : (n : ℕ) (X : UU-Fin l1 n) → UU l2)
  ( R : (n : ℕ) (X : UU-Fin l1 n) → Eq-Rel l3 (D n X))
  ( is-decidable-R : (n : ℕ) (X : UU-Fin l1 n) (a b : D n X) →
    is-decidable (sim-Eq-Rel (R n X) a b))
  ( equiv-D/R-fin-2-equiv : (n : ℕ) (X : UU-Fin l1 n) →
    leq-ℕ 2 n → Fin n ≃ type-UU-Fin n X →
    Fin 2 ≃ equivalence-class (R n X))
  ( invertible-action-D-equiv : (n : ℕ) (X X' : UU-Fin l1 n) →
    (type-UU-Fin n X ≃ type-UU-Fin n X') → D n X ≃ D n X')
  ( preserves-id-equiv-invertible-action-D-equiv : (n : ℕ) →
    ( X : UU-Fin l1 n) →
    Id (invertible-action-D-equiv n X X id-equiv) id-equiv)
  ( preserves-R-invertible-action-D-equiv : (n : ℕ) →
    ( X X' : UU-Fin l1 n) (e : type-UU-Fin n X ≃ type-UU-Fin n X') →
    ( a a' : D n X) →
    ( sim-Eq-Rel (R n X) a a' ↔
      sim-Eq-Rel
        ( R n X')
        ( map-equiv (invertible-action-D-equiv n X X' e) a)
        ( map-equiv (invertible-action-D-equiv n X X' e) a')))
  ( quotient-aut-succ-succ-Fin : (n : ℕ) →
    ( raise-Fin l1 (succ-ℕ (succ-ℕ n)) ≃
      raise-Fin l1 (succ-ℕ (succ-ℕ n))) →
    D
      ( succ-ℕ (succ-ℕ n))
      ( ( raise-Fin l1 (succ-ℕ (succ-ℕ n)),
        unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
  ( not-R-transposition-fin-succ-succ : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l1
      ( raise-Fin l1 (succ-ℕ (succ-ℕ n)))) →
    ¬ ( sim-Eq-Rel
      ( R (succ-ℕ (succ-ℕ n))
        ( pair
          ( raise-Fin l1 (succ-ℕ (succ-ℕ n)))
          ( unit-trunc-Prop
            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
        ( quotient-aut-succ-succ-Fin n (transposition Y))
        ( map-equiv
          ( invertible-action-D-equiv
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop
                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
            ( pair
              ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop
                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
            ( transposition Y))
          ( quotient-aut-succ-succ-Fin n (transposition Y)))))

  where

  private
    l4 : Level
    l4 = l2 ⊔ lsuc l3

    raise-UU-Fin-Fin : (n : ℕ) → UU-Fin l1 n
    pr1 (raise-UU-Fin-Fin n) = raise l1 (Fin n)
    pr2 (raise-UU-Fin-Fin n) = unit-trunc-Prop (compute-raise-Fin l1 n)

    quotient-loop-Fin : (n : ℕ) →
      type-Group
        ( loop-group-Set
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))) →
      ( D
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))) ≃
        D
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
    quotient-loop-Fin n p =
      invertible-action-D-equiv
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( p))

    map-quotient-loop-Fin : (n : ℕ) →
      type-Group
        ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))) →
      D
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))) →
      D
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
    map-quotient-loop-Fin n p =
      map-equiv (quotient-loop-Fin n p)

    quotient-set-Fin : (n : ℕ) → Set l4
    quotient-set-Fin n = equivalence-class-Set (R n (raise-UU-Fin-Fin n))

    quotient-map-quotient-Fin : (n : ℕ) →
      D n (raise-UU-Fin-Fin n) →
      type-Set (quotient-set-Fin n)
    quotient-map-quotient-Fin n =
      class
        ( R n (raise-UU-Fin-Fin n))

    quotient-reflecting-map-quotient-Fin : (n : ℕ) →
      reflecting-map-Eq-Rel
        ( R n (raise-UU-Fin-Fin n))
        ( type-Set (quotient-set-Fin n))
    quotient-reflecting-map-quotient-Fin n =
      quotient-reflecting-map-equivalence-class
        ( R n (raise-UU-Fin-Fin n))

  mere-equiv-D/R-fin-2 : (n : ℕ) (X : UU-Fin l1 n) →
    leq-ℕ 2 n →
    mere-equiv (Fin 2) (equivalence-class (R n X))
  mere-equiv-D/R-fin-2 n X ineq =
    map-trunc-Prop
      ( equiv-D/R-fin-2-equiv n X ineq)
      ( has-cardinality-type-UU-Fin n X)

  map-quotient-delooping-sign : (n : ℕ) →
    classifying-type-Concrete-Group
      ( UU-Fin-Group l1 n) →
    classifying-type-Concrete-Group
      ( UU-Fin-Group l4 2)
  map-quotient-delooping-sign zero-ℕ X = Fin-UU-Fin l4 2
  map-quotient-delooping-sign (succ-ℕ zero-ℕ) X = Fin-UU-Fin l4 2
  pr1 (map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)) X) =
    equivalence-class (R (succ-ℕ (succ-ℕ n)) X)
  pr2 (map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)) X) =
    mere-equiv-D/R-fin-2 (succ-ℕ (succ-ℕ n)) X star

  quotient-delooping-sign : (n : ℕ) →
    hom-Concrete-Group (UU-Fin-Group l1 n) (UU-Fin-Group l4 2)
  pr1 (quotient-delooping-sign n) = map-quotient-delooping-sign n
  pr2 (quotient-delooping-sign zero-ℕ) = refl
  pr2 (quotient-delooping-sign (succ-ℕ zero-ℕ)) = refl
  pr2 (quotient-delooping-sign (succ-ℕ (succ-ℕ n))) =
    eq-pair-Σ
      ( eq-equiv
        ( pr1
          ( map-quotient-delooping-sign
            ( succ-ℕ (succ-ℕ n))
            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
        ( raise l4 (Fin 2))
        ( ( compute-raise-Fin l4 2) ∘e
          ( inv-equiv
            ( equiv-D/R-fin-2-equiv
              ( succ-ℕ (succ-ℕ n))
              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
              ( star)
              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
      ( eq-is-prop is-prop-type-trunc-Prop)

  map-quotient-delooping-sign-loop : (n : ℕ) (X Y : UU l1) →
    (eX : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) X) →
    (eY : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) Y) →
    Id X Y →
    Id
      ( equivalence-class (R (succ-ℕ (succ-ℕ n)) (pair X eX)))
      ( equivalence-class (R (succ-ℕ (succ-ℕ n)) (pair Y eY)))
  map-quotient-delooping-sign-loop n X Y eX eY p =
    ap
      ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))

  private
    map-quotient-delooping-sign-loop-Fin : (n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))) →
      type-Group (loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
    map-quotient-delooping-sign-loop-Fin n =
      map-quotient-delooping-sign-loop n
        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
        ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
        ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))

  quotient-delooping-sign-loop : (n : ℕ) →
    type-hom-Group
      ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
      ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
  pr1 (quotient-delooping-sign-loop n) = map-quotient-delooping-sign-loop-Fin n
  pr2 (quotient-delooping-sign-loop n) p q =
    ( ap
      ( ap (λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z)))
      ( ( ap
        ( λ w → eq-pair-Σ (p ∙ q) w)
        ( eq-is-prop
          ( is-trunc-Id
            ( is-prop-type-trunc-Prop _ (unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))) ∙
        ( inv
          ( comp-eq-pair-Σ
            ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
            ( p)
            ( q)
            ( eq-is-prop is-prop-type-trunc-Prop)
            ( eq-is-prop is-prop-type-trunc-Prop))))) ∙
      ( ap-concat
        ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))
        ( eq-pair-Σ q (eq-is-prop is-prop-type-trunc-Prop)))

  abstract
    coherence-square-map-quotient-delooping-sign-loop-Set : (n : ℕ) →
      ( X Y : UU l1) ( eX : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) X) →
      ( eY : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) Y) →
      ( p : Id X Y) →
      ( Id (tr (λ v → mere-equiv (Fin (succ-ℕ (succ-ℕ n))) v) p eX) eY) →
      ( sX : is-set X) ( sY : is-set Y) →
      coherence-square-maps
        ( map-equiv
          ( invertible-action-D-equiv
            ( succ-ℕ (succ-ℕ n))
            ( pair Y eY)
            ( pair X eX)
            ( map-hom-symmetric-group-loop-group-Set
              ( pair X sX)
              ( pair Y sY)
              ( p))))
        ( class
          ( R (succ-ℕ (succ-ℕ n)) (pair Y eY)))
        ( class
          ( R (succ-ℕ (succ-ℕ n)) (pair X eX)))
        ( map-equiv
          ( map-hom-symmetric-group-loop-group-Set
            ( equivalence-class-Set (R (succ-ℕ (succ-ℕ n)) (pair X eX)))
            ( equivalence-class-Set (R (succ-ℕ (succ-ℕ n)) (pair Y eY)))
            ( map-quotient-delooping-sign-loop n X Y eX eY p)))
    coherence-square-map-quotient-delooping-sign-loop-Set n X .X eX .eX refl refl sX sY x =
      ( ap
        ( λ w →
          map-equiv
            ( map-hom-symmetric-group-loop-group-Set
              ( equivalence-class-Set (R (succ-ℕ (succ-ℕ n)) (pair X eX)))
              ( equivalence-class-Set (R (succ-ℕ (succ-ℕ n)) (pair X eX)))
              ( w))
            ( class
              ( R (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( x)))
        ( ap
          ( λ w → ap (λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z)) (eq-pair-Σ refl w))
          { x = eq-is-prop is-prop-type-trunc-Prop}
          ( eq-is-prop
            ( is-trunc-Id
              ( is-prop-type-trunc-Prop
                ( tr (mere-equiv (Fin (succ-ℕ (succ-ℕ n)))) refl eX)
                ( eX)))))) ∙
        ap
          ( class
            ( R
              ( succ-ℕ (succ-ℕ n))
              ( pair X (tr (mere-equiv (Fin (succ-ℕ (succ-ℕ n)))) refl eX))))
          ( inv
            ( htpy-eq-equiv
              ( preserves-id-equiv-invertible-action-D-equiv (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( x)))

  coherence-square-map-quotient-delooping-sign-loop-Fin : (n : ℕ)
    ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) →
    coherence-square-maps
      ( map-quotient-loop-Fin n p)
      ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
      ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
      ( map-equiv
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
          ( map-quotient-delooping-sign-loop-Fin n p)))
  coherence-square-map-quotient-delooping-sign-loop-Fin n p =
    coherence-square-map-quotient-delooping-sign-loop-Set n
      ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
      ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
      ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
      ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
      ( p)
      ( eq-is-prop is-prop-type-trunc-Prop)
      ( is-set-type-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
      ( is-set-type-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))

  private
    is-contr-equiv-quotient : (n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) →
      is-contr
        ( Σ
          ( type-Group
            ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
          ( λ h' →
            coherence-square-maps
              ( map-quotient-loop-Fin n p)
              ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
              ( map-reflecting-map-Eq-Rel
                ( R (succ-ℕ (succ-ℕ n))
                  ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
                ( quotient-reflecting-map-quotient-Fin (succ-ℕ (succ-ℕ n))))
              ( map-equiv h')))
    is-contr-equiv-quotient n p =
      unique-equiv-is-set-quotient
        ( R (succ-ℕ (succ-ℕ n)) (raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-reflecting-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
        ( R (succ-ℕ (succ-ℕ n)) (raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-reflecting-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
        ( is-set-quotient-equivalence-class
          ( R (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
        ( is-set-quotient-equivalence-class
          ( R (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
        ( ( quotient-loop-Fin n p) ,
          ( λ {x} {y} →
            preserves-R-invertible-action-D-equiv
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( p))
              ( x)
              ( y)))

  abstract
    eq-quotient-delooping-sign-loop-equiv-is-set-quotient : (n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) →
      Id
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
          ( map-quotient-delooping-sign-loop-Fin n p))
        ( pr1 (center (is-contr-equiv-quotient n p)))
    eq-quotient-delooping-sign-loop-equiv-is-set-quotient n p =
      ap pr1
        { x =
          pair
            ( map-hom-symmetric-group-loop-group-Set
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
              ( map-quotient-delooping-sign-loop-Fin n p))
            ( coherence-square-map-quotient-delooping-sign-loop-Fin n p)}
        { y = center (is-contr-equiv-quotient n p)}
        ( eq-is-contr (is-contr-equiv-quotient n p))

  cases-map-quotient-aut-Fin : (n : ℕ) →
    ( h : type-Group (symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) →
    ( is-decidable
      ( sim-Eq-Rel
        ( R (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-aut-succ-succ-Fin n h)
        ( map-equiv
          ( invertible-action-D-equiv
            (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( h))
          ( quotient-aut-succ-succ-Fin n h)))) →
    type-Group
      ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
  cases-map-quotient-aut-Fin n h (inl D) = id-equiv
  cases-map-quotient-aut-Fin n h (inr ND) =
     equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
      ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
      ( star)
      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))) ∘e
      ( ( equiv-succ-Fin 2) ∘e
        ( inv-equiv
          ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))

  map-quotient-aut-Fin : (n : ℕ) →
    type-Group (symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))) →
    type-Group
      ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
  map-quotient-aut-Fin n h =
    cases-map-quotient-aut-Fin n h
      ( is-decidable-R
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-aut-succ-succ-Fin n h)
        ( map-equiv
          ( invertible-action-D-equiv
            (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( h))
          ( quotient-aut-succ-succ-Fin n h)))

  eq-map-quotient-aut-fin-transposition : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l1 (raise l1 (Fin (succ-ℕ (succ-ℕ n))))) →
    Id
      ( map-quotient-aut-Fin n (transposition Y))
      ( ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( star)
        ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))) ∘e
        ( ( equiv-succ-Fin 2) ∘e
          ( inv-equiv
            ( equiv-D/R-fin-2-equiv
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( star)
              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
  eq-map-quotient-aut-fin-transposition n Y =
    ap
      ( cases-map-quotient-aut-Fin n (transposition Y))
      { x =
        is-decidable-R
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( quotient-aut-succ-succ-Fin n (transposition Y))
          ( map-equiv
            ( invertible-action-D-equiv
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( transposition Y))
            ( quotient-aut-succ-succ-Fin n (transposition Y)))}
      { y = inr (not-R-transposition-fin-succ-succ n Y)}
      ( eq-is-prop
        ( is-prop-is-decidable
          ( is-prop-sim-Eq-Rel
            ( R (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( quotient-aut-succ-succ-Fin n (transposition Y))
            ( map-equiv
              ( invertible-action-D-equiv
                ( succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( transposition Y))
              ( quotient-aut-succ-succ-Fin n (transposition Y))))))

  cases-eq-map-quotient-aut-Fin : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) →
    ( D : is-decidable
      ( sim-Eq-Rel
        ( R (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-aut-succ-succ-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p)))
        ( map-quotient-loop-Fin n p
          ( quotient-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( p)))))) →
    ( k k' : Fin 2) →
    Id
      ( map-inv-equiv
        ( equiv-D/R-fin-2-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
        ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
          ( quotient-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( p)))))
      ( k) →
    Id
      ( map-inv-equiv
        ( equiv-D/R-fin-2-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
        ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
          ( map-quotient-loop-Fin n p
            ( quotient-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( p))))))
      ( k') →
    Id
      ( map-equiv
        ( cases-map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p))
          ( D))
        ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
          ( quotient-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( p)))))
      ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
        ( map-quotient-loop-Fin n p
          ( quotient-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( p)))))
  cases-eq-map-quotient-aut-Fin n p (inl D) k k' q r =
    reflects-map-reflecting-map-Eq-Rel
      ( R (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
      ( quotient-reflecting-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
      ( D)
  cases-eq-map-quotient-aut-Fin n p (inr ND) (inl (inr star)) (inl (inr star)) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( R (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
            ( quotient-reflecting-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
            ( is-set-quotient-equivalence-class
              ( R (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
            ( quotient-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( p)))
            ( map-quotient-loop-Fin n p
              ( quotient-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                  ( p)))))
          ( is-injective-map-equiv
            ( inv-equiv
              ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
            ( q ∙ inv r))))
  cases-eq-map-quotient-aut-Fin n p (inr ND) (inl (inr star)) (inr star) q r =
    ( ap
      ( map-equiv
        ( equiv-D/R-fin-2-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
      ( ( ap
        ( map-equiv (equiv-succ-Fin 2))
        ( q)) ∙
        ( inv r))) ∙
       ap
        ( λ e →
          map-equiv e
            ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
              ( map-quotient-loop-Fin n p
                ( quotient-aut-succ-succ-Fin n
                  ( map-hom-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                    ( p))))))
        ( right-inverse-law-equiv
          ( equiv-D/R-fin-2-equiv
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
  cases-eq-map-quotient-aut-Fin n p (inr ND) (inr star) (inl (inr star)) q r =
    ( ap
      ( map-equiv
        ( equiv-D/R-fin-2-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
      ( ( ap
        ( map-equiv (equiv-succ-Fin 2))
        ( q)) ∙
        ( inv r))) ∙
       ap
        ( λ e →
          map-equiv e
            ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
              ( map-quotient-loop-Fin n p
                ( quotient-aut-succ-succ-Fin n
                  ( map-hom-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                    ( p))))))
        ( right-inverse-law-equiv
          ( equiv-D/R-fin-2-equiv
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
  cases-eq-map-quotient-aut-Fin n p (inr ND) (inr star) (inr star) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( R (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
            ( quotient-reflecting-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
            ( is-set-quotient-equivalence-class
              ( R (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
            ( quotient-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( p)))
            ( map-quotient-loop-Fin n p
              ( quotient-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                  ( p)))))
          ( is-injective-map-equiv
            ( inv-equiv
              ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
            ( q ∙ inv r))))

  eq-map-quotient-aut-Fin : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) →
    Id
      ( map-equiv
        ( map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p)))
        ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
          ( quotient-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( p)))))
      ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
        ( map-quotient-loop-Fin n p
          ( quotient-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
              ( p)))))
  eq-map-quotient-aut-Fin n p =
     cases-eq-map-quotient-aut-Fin n p
      ( is-decidable-R (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-aut-succ-succ-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p)))
        ( map-quotient-loop-Fin n p
          ( quotient-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p)))))
        ( map-inv-equiv
          ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
          ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
            ( quotient-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                ( p)))))
        ( map-inv-equiv
          ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
          ( quotient-map-quotient-Fin (succ-ℕ (succ-ℕ n))
            ( map-quotient-loop-Fin n p
              ( quotient-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                  ( p))))))
        ( refl)
        ( refl)

  eq-map-quotient-aut-loop-equiv-is-set-quotient : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) →
    Id
      ( map-quotient-aut-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( p)))
      ( pr1 (center (is-contr-equiv-quotient n p)))
  eq-map-quotient-aut-loop-equiv-is-set-quotient n p =
    eq-equiv-eq-one-value-equiv-is-set-quotient
      ( R (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
      ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
      ( quotient-reflecting-map-quotient-Fin (succ-ℕ (succ-ℕ n)))
      ( is-set-quotient-equivalence-class
        ( R (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
      ( inv-equiv
        ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
      ( map-quotient-loop-Fin n p)
      ( λ {x} {y} →
        preserves-R-invertible-action-D-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p))
          ( x)
          ( y))
      ( map-equiv
        ( map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p))))
      ( quotient-aut-succ-succ-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( p)))
      ( eq-map-quotient-aut-Fin n p)
      ( is-equiv-map-equiv (quotient-loop-Fin n p))
      ( is-equiv-map-equiv
        ( map-quotient-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
            ( p))))

  eq-quotient-delooping-sign-loop-sign-homomorphism : {l4 : Level} (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-delooping-sign-loop n)
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( symmetric-Group (Fin-Set 2))
          ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
          ( comp-hom-Group
            ( symmetric-Group (Fin-Set 2))
            ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
            ( hom-inv-symmetric-group-loop-group-Set
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
            ( hom-symmetric-group-equiv-Set
              ( Fin-Set 2)
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
              ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
          ( sign-homomorphism (succ-ℕ (succ-ℕ n))
            ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
  eq-quotient-delooping-sign-loop-sign-homomorphism n =
    map-inv-equiv
      ( equiv-ap-emb
        ( restriction-generating-subset-Group
          ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
          ( is-transposition-permutation-Prop {l2 = l1})
          ( tr
            ( λ s →
              is-generating-subset-Group
                ( symmetric-Group (pair (raise l1 (Fin (succ-ℕ (succ-ℕ n)))) s))
                ( is-transposition-permutation-Prop))
            ( eq-is-prop (is-prop-is-set (raise l1 (Fin (succ-ℕ (succ-ℕ n))))))
            ( is-generated-transposition-symmetric-Fin-Level
              ( succ-ℕ (succ-ℕ n))
              ( pair
                ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
          ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))))
      ( eq-htpy
        ( λ (pair f s) →
          apply-universal-property-trunc-Prop s
            ( Id-Prop
              ( set-Group (loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-subset-Group
                        ( symmetric-Group (pair (raise l1 (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l1 (Fin (succ-ℕ (succ-ℕ n))))))
                    ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                      ( pair
                        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                        ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                  ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( quotient-delooping-sign-loop n)
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
                ( pair f s))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-subset-Group
                        ( symmetric-Group (pair (raise l1 (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l1 (Fin (succ-ℕ (succ-ℕ n))))))
                    ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                      ( pair
                        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                        ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                    ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( comp-hom-Group
                    ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                    ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                    ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( comp-hom-Group
                      ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                      ( symmetric-Group (Fin-Set 2))
                      ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( comp-hom-Group
                        ( symmetric-Group (Fin-Set 2))
                        ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( hom-inv-symmetric-group-loop-group-Set
                          ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( hom-symmetric-group-equiv-Set (Fin-Set 2)
                          ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
                          ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
                      ( sign-homomorphism (succ-ℕ (succ-ℕ n))
                        ( pair
                          ( Fin (succ-ℕ (succ-ℕ n)))
                          ( unit-trunc-Prop id-equiv))))
                    ( hom-inv-symmetric-group-equiv-Set
                      ( Fin-Set (succ-ℕ (succ-ℕ n)))
                      ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
                ( pair f s)))
             λ (pair Y q) →
              ( eq-map-restriction-generating-subset-Group
                ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                ( is-transposition-permutation-Prop)
                ( tr
                  ( λ s₁ →
                     is-generating-subset-Group
                      ( symmetric-Group (pair (raise l1 (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                      ( is-transposition-permutation-Prop))
                  ( eq-is-prop (is-prop-is-set (raise l1 (Fin (succ-ℕ (succ-ℕ n))))))
                  ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                    ( pair
                      ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( quotient-delooping-sign-loop n)
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
                ( pair f s)) ∙
                ( ( htpy-eq-hom-Group
                  ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( id-hom-Group (loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( comp-hom-Group
                    ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( hom-inv-symmetric-group-loop-group-Set
                      ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( hom-symmetric-group-loop-group-Set
                      ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( inv
                    ( is-retr-hom-inv-symmetric-group-loop-group-Set
                      ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( ap (λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                    ( eq-pair-Σ
                     ( inv
                      ( eq-equiv
                        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                        ( f)))
                     ( eq-is-prop is-prop-type-trunc-Prop)))) ∙
                  ( ( ap
                    ( map-hom-Group
                      ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( hom-inv-symmetric-group-loop-group-Set
                        ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                    ( eq-quotient-delooping-sign-loop-equiv-is-set-quotient n
                      ( inv
                        ( eq-equiv
                          ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                          ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                          ( f))) ∙
                      ( inv
                        ( eq-map-quotient-aut-loop-equiv-is-set-quotient n
                          ( inv
                            ( eq-equiv
                              ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                              ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                              ( f))))))) ∙
                    ( ( ap
                      ( λ g →
                        map-hom-Group
                          ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( hom-inv-symmetric-group-loop-group-Set
                            ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( map-quotient-aut-Fin n g))
                      ( ( commutative-inv-map-hom-symmetric-group-loop-group-Set
                          ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                          ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                          ( eq-equiv
                            ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                            ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                            ( f))
                          ( pr2 (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                          ( pr2 (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) ∙
                          ( ap inv-equiv
                            ( ( ap
                              ( map-hom-symmetric-group-loop-group-Set
                                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                              ( ( ap
                                ( eq-equiv
                                  ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                                  ( raise l1 (Fin (succ-ℕ (succ-ℕ n)))))
                                ( inv (inv-inv-equiv f))) ∙
                                ( inv
                                  ( commutativity-inv-eq-equiv
                                    ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                                    ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                                    ( inv-equiv f))))) ∙
                              ( ( htpy-eq-hom-Group
                                ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                                ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                                ( comp-hom-Group
                                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                                  ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                                  ( hom-symmetric-group-loop-group-Set
                                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                                  ( hom-inv-symmetric-group-loop-group-Set
                                    ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
                                ( id-hom-Group
                                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
                                ( is-sec-hom-inv-symmetric-group-loop-group-Set
                                  ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                                ( inv-equiv f)) ∙
                                ( ( ap inv-equiv (inv q)) ∙
                                  ( own-inverse-is-involution
                                    ( is-involution-map-transposition Y)))))))) ∙
                      ( ( ap
                        ( map-hom-Group
                          ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( hom-inv-symmetric-group-loop-group-Set
                            ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                        ( ( ap
                          ( map-quotient-aut-Fin n)
                          ( own-inverse-is-involution
                            ( is-involution-map-transposition Y))) ∙
                          ( ( eq-map-quotient-aut-fin-transposition n Y) ∙
                            ( ap
                              ( λ e →
                                ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                                  ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                  ( star)
                                  ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))) ∘e
                                  ( e ∘e
                                    ( inv-equiv
                                      ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                                        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                        ( star)
                                        ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                              ( ( inv
                                ( eq-sign-homomorphism-transposition (succ-ℕ (succ-ℕ n))
                                  ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))
                                  ( map-equiv
                                    ( equiv-universes-2-Element-Decidable-Subtype
                                      ( Fin (succ-ℕ (succ-ℕ n)))
                                      ( l1)
                                      ( lzero))
                                    ( transposition-conjugation-equiv {l4 = l1}
                                      ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                                      ( Fin (succ-ℕ (succ-ℕ n)))
                                      ( inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
                                      ( Y))))) ∙
                                ( ap
                                  ( map-hom-Group
                                    ( symmetric-Group
                                      ( set-UU-Fin (succ-ℕ (succ-ℕ n))
                                       ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
                                    ( symmetric-Group (Fin-Set 2))
                                    ( sign-homomorphism
                                      ( succ-ℕ (succ-ℕ n))
                                      ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
                                  ( ( inv
                                    ( eq-equiv-universes-transposition (Fin (succ-ℕ (succ-ℕ n)))
                                      ( l1)
                                      ( lzero)
                                      ( transposition-conjugation-equiv
                                        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                                        ( Fin (succ-ℕ (succ-ℕ n)))
                                        ( inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
                                        ( Y)))) ∙
                                    ( ( eq-htpy-equiv
                                      ( correct-transposition-conjugation-equiv
                                        ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                                        ( Fin (succ-ℕ (succ-ℕ n)))
                                        ( inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
                                        ( Y))) ∙
                                      ( ( associative-comp-equiv
                                        ( inv-equiv (inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
                                        ( transposition Y)
                                        ( inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))) ∙
                                        ( ( ap
                                          ( λ e →
                                            inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))) ∘e
                                              ( transposition Y ∘e e))
                                          ( inv-inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))) ∙
                                          ( ap
                                            ( λ e →
                                              inv-equiv (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))) ∘e
                                                ( e ∘e compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))
                                            ( q)))))))))))) ∙
                        ( inv
                          ( eq-map-restriction-generating-subset-Group
                            ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                            ( is-transposition-permutation-Prop)
                            ( tr
                              ( λ s →
                                 is-generating-subset-Group
                                  ( symmetric-Group (pair (raise l1 (Fin (succ-ℕ (succ-ℕ n)))) s))
                                  ( is-transposition-permutation-Prop))
                              ( eq-is-prop (is-prop-is-set (raise l1 (Fin (succ-ℕ (succ-ℕ n))))))
                              ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                                ( pair
                                  ( raise l1 (Fin (succ-ℕ (succ-ℕ n))))
                                  ( unit-trunc-Prop (compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                            ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                            ( comp-hom-Group
                              ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                              ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                              ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                              ( comp-hom-Group
                                ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                                ( symmetric-Group (Fin-Set 2))
                                ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                                ( comp-hom-Group
                                  ( symmetric-Group (Fin-Set 2))
                                  ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( hom-inv-symmetric-group-loop-group-Set
                                    ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( hom-symmetric-group-equiv-Set
                                    ( Fin-Set 2)
                                    ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
                                    ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                                      ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
                                ( sign-homomorphism (succ-ℕ (succ-ℕ n))
                                  ( pair
                                    ( Fin (succ-ℕ (succ-ℕ n)))
                                    ( unit-trunc-Prop id-equiv))))
                              ( hom-inv-symmetric-group-equiv-Set
                                ( Fin-Set (succ-ℕ (succ-ℕ n)))
                                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
                            ( pair f s)))))))))

  eq-quotient-delooping-loop-UU-Fin-Group : (n : ℕ) →
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group l4 2))
        ( hom-iso-Group
          ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l4 2))
          ( comp-iso-Group
            ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l4 2))
            ( inv-iso-Group
              ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
              ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
              ( iso-loop-group-fin-UU-Fin-Group l4 2))
            ( iso-loop-group-equiv-Set
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-Set l4 (Fin-Set 2))
              ( ( compute-raise-Fin l4 2) ∘e
                ( inv-equiv
                  ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                    ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                    ( star)
                    ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))))
        ( quotient-delooping-sign-loop n))
      ( comp-hom-Group
        ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group l4 2))
        ( hom-group-hom-Concrete-Group
          ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n)))
          ( UU-Fin-Group l4 2)
          ( quotient-delooping-sign (succ-ℕ (succ-ℕ n))))
        ( hom-iso-Group
          ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
          ( inv-iso-Group
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
            ( iso-loop-group-fin-UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))))
  eq-quotient-delooping-loop-UU-Fin-Group n =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( λ r → eq-pair-Σ r (eq-is-prop is-prop-type-trunc-Prop))
            ( ap inv
              ( inv
                ( comp-eq-equiv
                  ( raise l4 (Fin 2))
                  ( equivalence-class
                    ( R (succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                  ( raise l4 (Fin 2))
                  ( ( equiv-eq
                    ( inv
                      ( ap
                        ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))) ∘e
                    ( inv-equiv
                      ( ( compute-raise-Fin l4 2) ∘e
                        ( inv-equiv
                          ( equiv-D/R-fin-2-equiv
                            ( succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                  ( ( compute-raise-Fin l4 2) ∘e
                    ( inv-equiv
                      ( equiv-D/R-fin-2-equiv
                        ( succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                        ( star)
                        ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))) ∙
                ( ap
                  ( λ r →
                    ( r) ∙
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( ( compute-raise-Fin l4 2) ∘e
                          ( inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                  (  inv
                    ( comp-eq-equiv
                      ( raise l4 (Fin 2))
                      ( equivalence-class
                        ( R (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                      ( equivalence-class
                        ( R (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                      ( inv-equiv
                        ( ( compute-raise-Fin l4 2) ∘e
                          ( inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                      ( equiv-eq
                        ( inv
                          ( ap
                            ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                            ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))) ∙
                    ( ( ap
                      ( λ r → r ∙
                        eq-equiv
                          ( equivalence-class
                            ( R (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                          ( equivalence-class
                            ( R (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                          ( equiv-eq
                            ( inv
                              ( ap
                                ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                                ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))))
                      ( inv
                        ( commutativity-inv-eq-equiv
                          ( equivalence-class
                            ( R (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                          ( raise l4 (Fin 2))
                          ( ( compute-raise-Fin l4 2) ∘e
                            ( inv-equiv
                              ( equiv-D/R-fin-2-equiv (succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                ( star)
                                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))) ∙
                      ( ap
                        ( λ e →
                          inv
                            ( eq-equiv
                              ( equivalence-class
                                ( R (succ-ℕ (succ-ℕ n))
                                  ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                              ( raise l4 (Fin 2))
                              ( ( compute-raise-Fin l4 2) ∘e
                                ( inv-equiv
                                  ( equiv-D/R-fin-2-equiv
                                    ( succ-ℕ (succ-ℕ n))
                                    ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                    ( star)
                                    ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))) ∙
                            ( map-equiv e
                              ( inv
                                ( ap
                                  ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                                  ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))))
                        ( left-inverse-law-equiv equiv-univalence)))))) ∙
              ( ( distributive-inv-concat
                ( ( inv
                  ( eq-equiv
                    ( equivalence-class
                      ( R (succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                    ( raise l4 (Fin 2))
                    ( ( compute-raise-Fin l4 2) ∘e
                      ( inv-equiv
                        ( equiv-D/R-fin-2-equiv
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                          ( star)
                          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))) ∙
                  ( inv
                    ( ap
                      ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))
                ( eq-equiv
                  ( equivalence-class
                    ( R (succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                  ( raise l4 (Fin 2))
                  ( ( compute-raise-Fin l4 2) ∘e
                    ( inv-equiv (equiv-D/R-fin-2-equiv
                      ( succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                      ( star)
                      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))) ∙
                ( ap
                  ( λ r →
                    inv
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( ( compute-raise-Fin l4 2) ∘e
                          ( inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))) ∙
                      ( r))
                  ( ( distributive-inv-concat
                    ( inv
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( ( compute-raise-Fin l4 2) ∘e
                          ( inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                    ( inv
                      ( ap
                        ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))) ∙
                    ( ap
                      ( λ r →
                        ( r) ∙
                          ( inv
                            ( inv
                              ( eq-equiv
                                ( equivalence-class
                                  ( R (succ-ℕ (succ-ℕ n))
                                    ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                                ( raise l4 (type-Set (Fin-Set 2)))
                                ( ( compute-raise-Fin l4 2) ∘e
                                  ( inv-equiv
                                    ( equiv-D/R-fin-2-equiv
                                      ( succ-ℕ (succ-ℕ n))
                                      ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))))
                      ( inv-inv
                        ( ap
                          ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                          ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))) ∙
                      ( ap
                        ( λ r →
                          ( ap
                            ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                            ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                            ( r))
                        ( inv-inv
                          ( eq-equiv
                            ( equivalence-class
                              ( R (succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                            ( raise l4 (Fin 2))
                            ( ( compute-raise-Fin l4 2) ∘e
                              ( inv-equiv
                                ( equiv-D/R-fin-2-equiv
                                  ( succ-ℕ (succ-ℕ n))
                                  ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                  ( star)
                                  ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))))))))))) ∙
            ( ( ( ap
              ( eq-pair-Σ
                ( ( inv
                  ( eq-equiv
                    ( equivalence-class
                      ( R (succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                    ( raise l4 (Fin 2))
                    ( ( compute-raise-Fin l4 2) ∘e
                      ( inv-equiv
                        ( equiv-D/R-fin-2-equiv
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                          ( star)
                          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))) ∙
                  ( ( ap
                    ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                    ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                    ( eq-equiv
                      ( equivalence-class
                        ( R (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                      ( raise l4 (Fin 2))
                      ( ( compute-raise-Fin l4 2) ∘e
                        ( inv-equiv
                          ( equiv-D/R-fin-2-equiv
                            ( succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))))
                ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
                ( ( inv
                  ( comp-eq-pair-Σ
                    ( pr2 (Fin-UU-Fin l4 2))
                    ( mere-equiv-D/R-fin-2
                      ( succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                      ( star))
                    ( pr2 (Fin-UU-Fin l4 2))
                    ( inv
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( ( compute-raise-Fin l4 2) ∘e
                          ( inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                    ( ( ap
                      ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( ( compute-raise-Fin l4 2) ∘e
                          ( inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                    ( eq-is-prop is-prop-type-trunc-Prop)
                    ( _))) ∙
                  ( ap
                    ( λ r →
                      ( eq-pair-Σ
                        ( inv
                          ( eq-equiv
                            ( equivalence-class
                              ( R (succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                            ( raise l4 (Fin 2))
                            ( ( compute-raise-Fin l4 2) ∘e
                              ( inv-equiv
                                ( equiv-D/R-fin-2-equiv
                                  ( succ-ℕ (succ-ℕ n))
                                  ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                  ( star)
                                  ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                        ( eq-is-prop is-prop-type-trunc-Prop)) ∙
                        ( r))
                    ( ( inv
                      ( comp-eq-pair-Σ
                        ( mere-equiv-D/R-fin-2
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                          ( star))
                        ( mere-equiv-D/R-fin-2
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                          ( star))
                        ( pr2 (Fin-UU-Fin l4 2))
                        ( ap
                          ( λ Z → equivalence-class (R (succ-ℕ (succ-ℕ n)) Z))
                          ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))
                        ( eq-equiv
                          ( equivalence-class
                            ( R
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                          ( raise l4 (Fin 2))
                          ( ( compute-raise-Fin l4 2) ∘e
                            ( inv-equiv
                              ( equiv-D/R-fin-2-equiv
                                ( succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                ( star)
                                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                        ( eq-is-prop is-prop-type-trunc-Prop)
                        ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( ap
                        ( λ r →
                          ( r) ∙
                            ( eq-pair-Σ
                              ( eq-equiv
                                ( equivalence-class
                                  ( R
                                    ( succ-ℕ (succ-ℕ n))
                                    ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                                ( raise l4 (Fin 2))
                                ( ( compute-raise-Fin l4 2) ∘e
                                  ( inv-equiv
                                    ( equiv-D/R-fin-2-equiv
                                      ( succ-ℕ (succ-ℕ n))
                                      ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))
                              ( eq-is-prop is-prop-type-trunc-Prop)))
                        ( ( ap
                          ( λ w → eq-pair-Σ (pr1 w) (pr2 w))
                          { y =
                            pair-eq-Σ
                              ( ap
                                ( map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)))
                                ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))}
                          ( eq-pair-Σ
                            ( inv
                              ( ap-pair-eq-Σ
                                ( UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                ( map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)))
                                ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))
                            ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _))))) ∙
                           issec-pair-eq-Σ
                            ( map-quotient-delooping-sign (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n))))
                            ( map-quotient-delooping-sign (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n))))
                            ( ap
                              ( map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)))
                              ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))))))) ∙
              ( ( ap
                ( λ r →
                  ( r) ∙
                    ( ( ap
                      ( map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( eq-pair-Σ
                        ( eq-equiv
                          ( equivalence-class
                            ( R (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                          ( raise l4 (Fin 2))
                          ( compute-raise-Fin l4 2 ∘e
                            inv-equiv
                              ( equiv-D/R-fin-2-equiv
                                ( succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                                ( star)
                                ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
                        ( eq-is-prop is-prop-type-trunc-Prop))))
                ( ( ap
                  ( eq-pair-Σ
                    ( inv
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( compute-raise-Fin l4 2 ∘e
                          inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                  ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
                  ( inv
                    ( inv-eq-pair-Σ
                      ( mere-equiv-D/R-fin-2
                        ( succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                        ( star))
                      ( pr2 (Fin-UU-Fin l4 2))
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( compute-raise-Fin l4 2 ∘e
                          inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
                      ( eq-is-prop is-prop-type-trunc-Prop))))) ∙
                ( inv
                  ( eq-tr-type-Ω
                    ( eq-pair-Σ
                      ( eq-equiv
                        ( equivalence-class
                          ( R (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))))
                        ( raise l4 (Fin 2))
                        ( compute-raise-Fin l4 2 ∘e
                          inv-equiv
                            ( equiv-D/R-fin-2-equiv
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l1 (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
                      (eq-is-prop is-prop-type-trunc-Prop))
                    ( ap (map-quotient-delooping-sign (succ-ℕ (succ-ℕ n)))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group
            ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
          ( semigroup-Group
            ( abstract-group-Concrete-Group (UU-Fin-Group l4 2)))
          ( pr1
            ( comp-hom-Group
              ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
              ( abstract-group-Concrete-Group
                ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
              ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
              ( hom-group-hom-Concrete-Group
                ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n)))
                ( UU-Fin-Group l4 2)
                ( quotient-delooping-sign (succ-ℕ (succ-ℕ n))))
              ( hom-iso-Group
                ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                ( abstract-group-Concrete-Group
                  ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
                ( inv-iso-Group
                  ( abstract-group-Concrete-Group
                    ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                  ( iso-loop-group-fin-UU-Fin-Group l1 (succ-ℕ (succ-ℕ n)))))))))

  symmetric-abstract-UU-fin-group-quotient-hom : (n : ℕ) →
    type-hom-Group
      ( symmetric-Group (Fin-Set 2))
      ( abstract-group-Concrete-Group
        ( UU-Fin-Group l4 2))
  symmetric-abstract-UU-fin-group-quotient-hom n =
    comp-hom-Group
      ( symmetric-Group (Fin-Set 2))
      ( symmetric-Group
        ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
      ( abstract-group-Concrete-Group
        ( UU-Fin-Group l4 2))
      ( comp-hom-Group
        ( symmetric-Group
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group l4 2))
        ( hom-iso-Group
          ( loop-group-Set
            ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l4 2))
          ( comp-iso-Group
            ( loop-group-Set
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set
              ( raise-Set l4 (Fin-Set 2)))
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l4 2))
            ( inv-iso-Group
              ( abstract-group-Concrete-Group
                ( UU-Fin-Group l4 2))
              ( loop-group-Set
                ( raise-Set l4 (Fin-Set 2)))
              ( iso-loop-group-fin-UU-Fin-Group l4 2))
            ( iso-loop-group-equiv-Set
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-Set l4 (Fin-Set 2))
              ( ( compute-raise-Fin l4 2) ∘e
                ( inv-equiv
                  ( equiv-D/R-fin-2-equiv
                    ( succ-ℕ (succ-ℕ n))
                    ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                    ( star)
                    ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))))
        ( hom-inv-symmetric-group-loop-group-Set
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
      ( hom-symmetric-group-equiv-Set
        ( Fin-Set 2)
        ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
        ( equiv-D/R-fin-2-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))

  eq-quotient-delooping-sign-homomorphism : (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group l4 2))
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l4 2))
          ( hom-group-hom-Concrete-Group
            ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n)))
            ( UU-Fin-Group l4 2)
            ( quotient-delooping-sign (succ-ℕ (succ-ℕ n))))
          ( hom-inv-iso-Group
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l1 (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
            ( iso-loop-group-fin-UU-Fin-Group l1 (succ-ℕ (succ-ℕ n)))))
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group l4 2))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( symmetric-Group (Fin-Set 2))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l4 2))
          ( symmetric-abstract-UU-fin-group-quotient-hom n)
          ( sign-homomorphism
            ( succ-ℕ (succ-ℕ n))
            ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
          ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))
  eq-quotient-delooping-sign-homomorphism n =
    ( ap
      ( λ f →
        comp-hom-Group
          ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
          ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
          ( f)
          ( hom-inv-symmetric-group-loop-group-Set
            ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
      ( inv (eq-quotient-delooping-loop-UU-Fin-Group n))) ∙
      ( ( associative-comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set
          ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group l4 2))
        ( hom-iso-Group
          ( loop-group-Set
            ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l4 2))
          ( comp-iso-Group
            ( loop-group-Set
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set
              ( raise-Set l4 (Fin-Set 2)))
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l4 2))
            ( inv-iso-Group
              ( abstract-group-Concrete-Group
                ( UU-Fin-Group l4 2))
              ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
              ( iso-loop-group-fin-UU-Fin-Group l4 2))
            ( iso-loop-group-equiv-Set
              ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-Set l4 (Fin-Set 2))
              ( compute-raise-Fin l4 2 ∘e
                inv-equiv
                  ( equiv-D/R-fin-2-equiv
                    (succ-ℕ (succ-ℕ n))
                    ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                    ( star)
                    ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
        ( quotient-delooping-sign-loop n)
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))) ∙
        ( ( ap
          ( λ f →
            comp-hom-Group
              ( symmetric-Group
                ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
              ( loop-group-Set
                ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
              ( abstract-group-Concrete-Group
                ( UU-Fin-Group l4 2))
              ( hom-iso-Group
                ( loop-group-Set
                  ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                ( abstract-group-Concrete-Group
                  ( UU-Fin-Group l4 2))
                ( comp-iso-Group
                  ( loop-group-Set
                    ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set
                    ( raise-Set l4 (Fin-Set 2)))
                  ( abstract-group-Concrete-Group
                    ( UU-Fin-Group l4 2))
                  ( inv-iso-Group
                    ( abstract-group-Concrete-Group
                      ( UU-Fin-Group l4 2))
                    ( loop-group-Set
                      ( raise-Set l4 (Fin-Set 2)))
                    ( iso-loop-group-fin-UU-Fin-Group l4 2))
                  ( iso-loop-group-equiv-Set
                    ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
                    ( raise-Set l4 (Fin-Set 2))
                    ( compute-raise-Fin l4 2 ∘e
                      inv-equiv
                      ( equiv-D/R-fin-2-equiv
                        ( succ-ℕ (succ-ℕ n))
                        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                        ( star)
                        ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
              ( f))
          ( eq-quotient-delooping-sign-loop-sign-homomorphism {l4 = l4} n)) ∙
          ( eq-pair-Σ
            ( refl)
            ( eq-is-prop
              ( is-prop-preserves-mul-Semigroup
                ( semigroup-Group
                  ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))))
                ( semigroup-Group
                  ( abstract-group-Concrete-Group (UU-Fin-Group l4 2)))
                ( pr1
                  ( comp-hom-Group
                    ( symmetric-Group (raise-Fin-Set l1 (succ-ℕ (succ-ℕ n))))
                    ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                    ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
                    ( comp-hom-Group
                      ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                      ( symmetric-Group (Fin-Set 2))
                      ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
                      ( comp-hom-Group
                        ( symmetric-Group (Fin-Set 2))
                        ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
                        ( comp-hom-Group
                          ( symmetric-Group (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
                          ( hom-iso-Group
                            ( loop-group-Set (quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                            ( abstract-group-Concrete-Group (UU-Fin-Group l4 2))
                            ( comp-iso-Group
                              ( loop-group-Set ( quotient-set-Fin (succ-ℕ (succ-ℕ n))))
                              ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
                              ( abstract-group-Concrete-Group
                                ( UU-Fin-Group l4 2))
                              ( inv-iso-Group
                                ( abstract-group-Concrete-Group
                                  ( UU-Fin-Group l4 2))
                                ( loop-group-Set (raise-Set l4 (Fin-Set 2)))
                                ( iso-loop-group-fin-UU-Fin-Group l4 2))
                              ( iso-loop-group-equiv-Set
                                ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
                                ( raise-Set l4 (Fin-Set 2))
                                ( compute-raise-Fin l4 2 ∘e
                                  inv-equiv
                                    ( equiv-D/R-fin-2-equiv
                                      ( succ-ℕ (succ-ℕ n))
                                      ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))))
                          ( hom-inv-symmetric-group-loop-group-Set
                            ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))))
                        ( hom-symmetric-group-equiv-Set
                          ( Fin-Set 2)
                          ( quotient-set-Fin (succ-ℕ (succ-ℕ n)))
                          ( equiv-D/R-fin-2-equiv
                            ( succ-ℕ (succ-ℕ n))
                            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n))))))
                      ( sign-homomorphism (succ-ℕ (succ-ℕ n))
                        ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
                    ( hom-inv-symmetric-group-equiv-Set (Fin-Set (succ-ℕ (succ-ℕ n)))
                      ( raise-Fin-Set l1 (succ-ℕ (succ-ℕ n)))
                      ( compute-raise-Fin l1 (succ-ℕ (succ-ℕ n)))))))))))
```
