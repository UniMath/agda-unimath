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

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.symmetric-groups

open import univalent-combinatorics.orientations-complete-undirected-graph
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

## Definitions

```agda
module _
  { l : Level}
  where

  cartier-delooping-sign : (n : ℕ) →
    hom-Concrete-Group (UU-Fin-Group l n) (UU-Fin-Group (lsuc l) 2)
  cartier-delooping-sign =
    quotient-delooping-sign
      ( orientation-Complete-Undirected-Graph)
      ( even-difference-orientation-Complete-Undirected-Graph)
      ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
      ( equiv-fin-2-quotient-sign-equiv-Fin)
      ( orientation-complete-undirected-graph-equiv)
      ( preserves-id-equiv-orientation-complete-undirected-graph-equiv)
      ( preserves-even-difference-orientation-complete-undirected-graph-equiv)
      ( λ n →
        orientation-aut-count
          ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
      ( λ n →
        not-even-difference-orientation-aut-transposition-count
          ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))

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
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
            ( equiv-fin-2-quotient-sign-equiv-Fin)
            ( orientation-complete-undirected-graph-equiv)
            ( preserves-id-equiv-orientation-complete-undirected-graph-equiv)
            ( preserves-even-difference-orientation-complete-undirected-graph-equiv)
            ( λ n →
              orientation-aut-count
                ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( star))
            ( λ n →
              not-even-difference-orientation-aut-transposition-count
                ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( star))
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
      ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
      ( equiv-fin-2-quotient-sign-equiv-Fin)
      ( orientation-complete-undirected-graph-equiv)
      ( preserves-id-equiv-orientation-complete-undirected-graph-equiv)
      ( preserves-even-difference-orientation-complete-undirected-graph-equiv)
      ( λ n →
        orientation-aut-count
          ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
      ( λ n →
        not-even-difference-orientation-aut-transposition-count
          ( pair (succ-ℕ (succ-ℕ n)) (compute-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
```
