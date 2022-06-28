# The group of n-element types

```agda
{-# OPTIONS --without-K --exact-split --experimental-lossy-unification #-}

module finite-group-theory.finite-type-groups where

open import elementary-number-theory.natural-numbers

open import foundation.connected-types 
open import foundation.dependent-pair-types 
open import foundation.equality-dependent-pair-types 
open import foundation.equivalences 
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.univalence 
open import foundation.universe-levels 

open import group-theory.concrete-groups 

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

```agda
UU-Fin-Level-Group : (l : Level) (n : ℕ) → Concrete-Group (lsuc l)
pr1 (pr1 (pr1 (UU-Fin-Level-Group l n))) = UU-Fin-Level l n
pr2 (pr1 (pr1 (UU-Fin-Level-Group l n))) = Fin-UU-Fin-Level l n
pr2 (pr1 (UU-Fin-Level-Group l n)) = is-path-connected-UU-Fin-Level n
pr2 (UU-Fin-Level-Group l n) =
  is-set-equiv
    ( equiv-UU-Fin-Level (Fin-UU-Fin-Level l n) (Fin-UU-Fin-Level l n))
    ( equiv-equiv-eq-UU-Fin-Level (Fin-UU-Fin-Level l n) (Fin-UU-Fin-Level l n))
    ( is-set-equiv-is-set
      ( is-set-type-Set (raise-Set l (Fin-Set n)))
      ( is-set-type-Set (raise-Set l (Fin-Set n))))
```


