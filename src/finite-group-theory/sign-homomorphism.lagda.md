# The sign homomorphism

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.sign-homomorphism where

open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( add-Fin; mod-two-ℕ; mod-succ-add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ)

open import finite-group-theory.permutations using
  ( is-contr-parity-transposition-permutation;
    list-transpositions-permutation-count;
    retr-permutation-list-transpositions-count)
open import finite-group-theory.transpositions using
  ( permutation-list-transpositions; eq-concat-permutation-list-transpositions)

open import foundation.automorphisms using (Aut)
open import foundation.contractible-types using (center; eq-is-contr)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; map-equiv)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using (Id; inv; _∙_; ap; refl)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.sets using (Id-Prop)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level)

open import group-theory.homomorphisms-groups using (type-hom-Group)
open import group-theory.homomorphisms-semigroups using (preserves-mul)
open import group-theory.symmetric-groups using (symmetric-Group)

open import univalent-combinatorics.2-element-types using
  ( aut-point-Fin-two-ℕ; is-involution-aut-Fin-two-ℕ;
    preserves-add-aut-point-Fin-two-ℕ)
open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin-Level)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Fin-Set)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; has-cardinality; mere-equiv-UU-Fin-Level)
open import univalent-combinatorics.lists using
  ( list; concat-list; length-list; length-concat-list)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; equiv-succ-Fin)
```

## Idea

The sign of a permutation is defined as the parity of the length of the decomposition of the permutation into transpositions. We show that each such decomposition as the same parity, so the sign map is well defined. We then show that the sign map is a group homomorphism.

## Definitions

### The sign homomorphism into ℤ/2

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) 
  where

  sign-homomorphism-Fin-two : Aut (type-UU-Fin-Level X) → Fin 2
  sign-homomorphism-Fin-two f =
    pr1 (center (is-contr-parity-transposition-permutation n X f))

  preserves-add-sign-homomorphism-Fin-two :
    (f g : (type-UU-Fin-Level X) ≃ (type-UU-Fin-Level X)) →
    Id ( sign-homomorphism-Fin-two (f ∘e g))
       ( add-Fin (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g))
  preserves-add-sign-homomorphism-Fin-two f g =
    apply-universal-property-trunc-Prop
      ( mere-equiv-UU-Fin-Level X)
      ( Id-Prop
        ( Fin-Set 2)
        ( sign-homomorphism-Fin-two (f ∘e g))
        ( add-Fin (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g)))
      ( λ h →
        ( ap
          ( pr1)
          ( eq-is-contr
            ( is-contr-parity-transposition-permutation n X (f ∘e g))
            { x =
              center (is-contr-parity-transposition-permutation n X (f ∘e g))}
            { y =
              pair
                ( mod-two-ℕ (length-list (list-comp-f-g h)))
                ( unit-trunc-Prop
                  ( pair
                    ( list-comp-f-g h)
                    ( pair refl (eq-list-comp-f-g h))))})) ∙
        ( ( ap
            ( mod-two-ℕ)
            ( length-concat-list (list-trans f h) (list-trans g h))) ∙
          ( ( mod-succ-add-ℕ 1
              ( length-list (list-trans f h))
              ( length-list (list-trans g h))) ∙
            ( ( ap
                ( λ P →
                  add-Fin (pr1 P) (mod-two-ℕ (length-list (list-trans g h))))
                { x =
                  pair
                    ( mod-two-ℕ (length-list (list-trans f h)))
                    ( unit-trunc-Prop
                      ( pair
                        ( list-trans f h)
                        ( pair
                          ( refl)
                          ( inv
                            ( eq-htpy-equiv
                              ( retr-permutation-list-transpositions-count
                                ( type-UU-Fin-Level X)
                                ( pair n h)
                                ( f)))))))}
                { y = center (is-contr-parity-transposition-permutation n X f)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X f))) ∙
              ( ap
                ( λ P → add-Fin (sign-homomorphism-Fin-two f) (pr1 P))
                { x =
                  pair
                    ( mod-two-ℕ (length-list (list-trans g h)))
                    ( unit-trunc-Prop
                      ( pair
                        ( list-trans g h)
                        ( pair
                          ( refl)
                          ( inv
                            ( eq-htpy-equiv
                              ( retr-permutation-list-transpositions-count
                                ( type-UU-Fin-Level X)
                                ( pair n h)
                                ( g)))))))}
                { y = center (is-contr-parity-transposition-permutation n X g)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X g)))))))
    where
    list-trans :
      ( f' : (type-UU-Fin-Level X) ≃ (type-UU-Fin-Level X))
      ( h : Fin n ≃ type-UU-Fin-Level X) →
      list
        ( Σ ( type-UU-Fin-Level X → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x)))))
    list-trans f' h =
      list-transpositions-permutation-count (type-UU-Fin-Level X) (pair n h) f'
    list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin-Level X) →
      list
        ( Σ ( (type-UU-Fin-Level X) → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x)))))
    list-comp-f-g h = concat-list (list-trans f h) (list-trans g h)
    eq-list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin-Level X) →
      Id ( f ∘e g)
         ( permutation-list-transpositions
           ( type-UU-Fin-Level X)
           ( list-comp-f-g h))
    eq-list-comp-f-g h =
      eq-htpy-equiv
        ( λ x →
          ( inv
            ( retr-permutation-list-transpositions-count
              ( type-UU-Fin-Level X)
              ( pair n h)
              ( f)
              ( map-equiv g x))) ∙
          ( ap
            ( map-equiv
              ( permutation-list-transpositions
                ( type-UU-Fin-Level X)
                ( list-trans f h)))
            ( inv
              ( retr-permutation-list-transpositions-count
                ( type-UU-Fin-Level X)
                ( pair n h)
                ( g)
                ( x))))) ∙
              ( eq-concat-permutation-list-transpositions
                ( type-UU-Fin-Level X)
                ( list-trans f h)
                ( list-trans g h))
```

### The sign homomorphism into the symmetric group S₂

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n)
  where

  map-sign-homomorphism : Aut (type-UU-Fin-Level X) → Aut (Fin 2)
  map-sign-homomorphism f =
    aut-point-Fin-two-ℕ (sign-homomorphism-Fin-two n X f)

  preserves-comp-map-sign-homomorphism :
    preserves-mul _∘e_ _∘e_ map-sign-homomorphism
  preserves-comp-map-sign-homomorphism f g =
    ( ap
      ( aut-point-Fin-two-ℕ)
      ( preserves-add-sign-homomorphism-Fin-two n X f g)) ∙
    ( preserves-add-aut-point-Fin-two-ℕ
      ( sign-homomorphism-Fin-two n X f)
      ( sign-homomorphism-Fin-two n X g))
  
  sign-homomorphism :
    type-hom-Group
      ( symmetric-Group (set-UU-Fin-Level X))
      ( symmetric-Group (Fin-Set 2))
  pr1 sign-homomorphism = map-sign-homomorphism
  pr2 sign-homomorphism = preserves-comp-map-sign-homomorphism
```

