# Cartier's delooping of the sign homomorphism

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module finite-group-theory.cartier-delooping-sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.delooping-sign-homomorphism
open import finite-group-theory.finite-type-groups
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.univalence-action-on-equivalences
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.symmetric-groups

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.orientations-complete-undirected-graph
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the delooping of the sign homomorphism by using a method of Cartier.

## Definitions

```agda
module _
  { l : Level}
  where

  not-even-difference-univalent-action-equiv : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l
      ( raise-Fin l (succ-ℕ (succ-ℕ n)))) →
    ¬ ( sim-Eq-Rel
      ( even-difference-orientation-Complete-Undirected-Graph
        (succ-ℕ (succ-ℕ n))
        ( pair
          ( raise-Fin l (succ-ℕ (succ-ℕ n)))
          ( unit-trunc-Prop
            ( compute-raise-Fin l (succ-ℕ (succ-ℕ n))))))
        ( orientation-aut-count
          ( succ-ℕ (succ-ℕ n) , compute-raise l (Fin (succ-ℕ (succ-ℕ n))))
          star (transposition Y))
        ( map-equiv
          ( univalent-action-equiv
            ( mere-equiv-Prop (Fin (succ-ℕ (succ-ℕ n))))
            ( orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n)))
            ( raise l (Fin (succ-ℕ (succ-ℕ n))) ,
              unit-trunc-Prop (compute-raise-Fin l (succ-ℕ (succ-ℕ n))))
            ( raise l (Fin (succ-ℕ (succ-ℕ n))) ,
              unit-trunc-Prop (compute-raise-Fin l (succ-ℕ (succ-ℕ n))))
            ( transposition Y))
          ( orientation-aut-count
            ( succ-ℕ (succ-ℕ n) , compute-raise l (Fin (succ-ℕ (succ-ℕ n))))
            star (transposition Y))))
  not-even-difference-univalent-action-equiv n =
    tr
      ( λ f →
        ( Y : 2-Element-Decidable-Subtype l
          ( raise-Fin l (succ-ℕ (succ-ℕ n)))) →
            ¬ ( sim-Eq-Rel
              ( even-difference-orientation-Complete-Undirected-Graph
                (succ-ℕ (succ-ℕ n))
                ( pair
                ( raise-Fin l (succ-ℕ (succ-ℕ n)))
                ( unit-trunc-Prop
                    ( compute-raise-Fin l (succ-ℕ (succ-ℕ n))))))
                ( orientation-aut-count
                    ( succ-ℕ (succ-ℕ n) , compute-raise l (Fin (succ-ℕ (succ-ℕ n))))
                    star (transposition Y))
                ( map-equiv
                  ( f
                    ( raise l (Fin (succ-ℕ (succ-ℕ n))) ,
                      unit-trunc-Prop (compute-raise-Fin l (succ-ℕ (succ-ℕ n))))
                    ( raise l (Fin (succ-ℕ (succ-ℕ n))) ,
                      unit-trunc-Prop (compute-raise-Fin l (succ-ℕ (succ-ℕ n))))
                    ( transposition Y))
                  ( orientation-aut-count
                    ( succ-ℕ (succ-ℕ n) , compute-raise l (Fin (succ-ℕ (succ-ℕ n))))
                    star (transposition Y)))))
      ( ap pr1
        { x =
          orientation-complete-undirected-graph-equiv (succ-ℕ (succ-ℕ n)) ,
            ( preserves-id-equiv-orientation-complete-undirected-graph-equiv
              ( succ-ℕ (succ-ℕ n)))}
        { y =
          ( univalent-action-equiv
            ( mere-equiv-Prop (Fin (succ-ℕ (succ-ℕ n))))
            ( orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n)))) ,
            ( preserves-id-equiv-univalent-action-equiv
              ( mere-equiv-Prop (Fin (succ-ℕ (succ-ℕ n))))
              ( orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))))}
        ( eq-is-contr
          ( is-contr-preserves-id-action-equiv
            ( mere-equiv-Prop (Fin (succ-ℕ (succ-ℕ n))))
            ( orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n)))
            ( λ X →
              is-set-orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n)) X))))
      ( not-even-difference-orientation-aut-transposition-count
        ( succ-ℕ (succ-ℕ n) , (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( star))

  cartier-delooping-sign : (n : ℕ) →
    hom-Concrete-Group (UU-Fin-Group l n) (UU-Fin-Group (lsuc l) 2)
  cartier-delooping-sign =
    quotient-delooping-sign
      ( orientation-Complete-Undirected-Graph)
      ( even-difference-orientation-Complete-Undirected-Graph)
      ( λ n H → is-decidable-even-difference-orientation-Complete-Undirected-Graph n)
      ( equiv-fin-2-quotient-sign-equiv-Fin)
      ( λ n →
        orientation-aut-count
          ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
      ( not-even-difference-univalent-action-equiv)

  eq-cartier-delooping-sign-homomorphism : (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group (lsuc l) 2))
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group (lsuc l) 2))
          ( hom-group-hom-Concrete-Group
            ( UU-Fin-Group l (succ-ℕ (succ-ℕ n)))
            ( UU-Fin-Group (lsuc l) 2)
            ( cartier-delooping-sign (succ-ℕ (succ-ℕ n))))
          ( hom-inv-iso-Group
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
            ( iso-loop-group-fin-UU-Fin-Group l (succ-ℕ (succ-ℕ n)))))
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group (lsuc l) 2))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( symmetric-Group (Fin-Set 2))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group (lsuc l) 2))
          ( symmetric-abstract-UU-fin-group-quotient-hom
            ( orientation-Complete-Undirected-Graph)
            ( even-difference-orientation-Complete-Undirected-Graph)
            ( λ n H → is-decidable-even-difference-orientation-Complete-Undirected-Graph n)
            ( equiv-fin-2-quotient-sign-equiv-Fin)
            ( λ n →
              orientation-aut-count
                ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( star))
            ( not-even-difference-univalent-action-equiv)
            ( n))
          ( sign-homomorphism
            ( succ-ℕ (succ-ℕ n))
            ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( compute-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  eq-cartier-delooping-sign-homomorphism =
    eq-quotient-delooping-sign-homomorphism
      ( orientation-Complete-Undirected-Graph)
      ( even-difference-orientation-Complete-Undirected-Graph)
      ( λ n H → is-decidable-even-difference-orientation-Complete-Undirected-Graph n)
      ( equiv-fin-2-quotient-sign-equiv-Fin)
      ( λ n →
        orientation-aut-count
          ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
      ( not-even-difference-univalent-action-equiv)
```

## References

- Mangel É. and Rijke E.
  ["Delooping the sign homomorphism in univalent mathematics"](https://arxiv.org/abs/2301.10011).
