# The sign homomorphism

```agda
module finite-group-theory.sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations
open import finite-group-theory.transpositions

open import foundation.automorphisms
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.symmetric-groups

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.lists
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sign of a permutation is defined as the parity of the length of the decomposition of the permutation into transpositions. We show that each such decomposition as the same parity, so the sign map is well defined. We then show that the sign map is a group homomorphism.

## Definitions

### The sign homomorphism into ℤ/2

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  sign-homomorphism-Fin-two : Aut (type-UU-Fin n X) → Fin 2
  sign-homomorphism-Fin-two f =
    pr1 (center (is-contr-parity-transposition-permutation n X f))

  preserves-add-sign-homomorphism-Fin-two :
    (f g : (type-UU-Fin n X) ≃ (type-UU-Fin n X)) →
    Id ( sign-homomorphism-Fin-two (f ∘e g))
       ( add-Fin 2 (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g))
  preserves-add-sign-homomorphism-Fin-two f g =
    apply-universal-property-trunc-Prop
      ( has-cardinality-type-UU-Fin n X)
      ( Id-Prop
        ( Fin-Set 2)
        ( sign-homomorphism-Fin-two (f ∘e g))
        ( add-Fin 2 (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g)))
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
                  add-Fin 2 (pr1 P) (mod-two-ℕ (length-list (list-trans g h))))
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
                                ( type-UU-Fin n X)
                                ( pair n h)
                                ( f)))))))}
                { y = center (is-contr-parity-transposition-permutation n X f)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X f))) ∙
              ( ap
                ( λ P → add-Fin 2 (sign-homomorphism-Fin-two f) (pr1 P))
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
                                ( type-UU-Fin n X)
                                ( pair n h)
                                ( g)))))))}
                { y = center (is-contr-parity-transposition-permutation n X g)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X g)))))))
    where
    list-trans :
      ( f' : (type-UU-Fin n X) ≃ (type-UU-Fin n X))
      ( h : Fin n ≃ type-UU-Fin n X) →
      list
        ( Σ ( type-UU-Fin n X → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin n X) (λ x → type-decidable-Prop (P x)))))
    list-trans f' h =
      list-transpositions-permutation-count (type-UU-Fin n X) (pair n h) f'
    list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin n X) →
      list
        ( Σ ( (type-UU-Fin n X) → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin n X) (λ x → type-decidable-Prop (P x)))))
    list-comp-f-g h = concat-list (list-trans f h) (list-trans g h)
    eq-list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin n X) →
      Id ( f ∘e g)
         ( permutation-list-transpositions
           ( list-comp-f-g h))
    eq-list-comp-f-g h =
      eq-htpy-equiv
        ( λ x →
          ( inv
            ( retr-permutation-list-transpositions-count
              ( type-UU-Fin n X)
              ( pair n h)
              ( f)
              ( map-equiv g x))) ∙
          ( ap
            ( map-equiv
              ( permutation-list-transpositions
                ( list-trans f h)))
            ( inv
              ( retr-permutation-list-transpositions-count
                ( type-UU-Fin n X)
                ( pair n h)
                ( g)
                ( x))))) ∙
              ( eq-concat-permutation-list-transpositions
                ( list-trans f h)
                ( list-trans g h))

  eq-sign-homomorphism-Fin-two-transposition :
    ( Y : 2-Element-Decidable-Subtype l (type-UU-Fin n X)) →
    Id
      ( sign-homomorphism-Fin-two (transposition Y))
      ( inr star)
  eq-sign-homomorphism-Fin-two-transposition Y =
    ap pr1
      { x = center (is-contr-parity-transposition-permutation n X (transposition Y))}
      { y =
        pair
          ( inr star)
          ( unit-trunc-Prop
            ( pair
              ( in-list Y)
              ( pair refl (inv (right-unit-law-equiv (transposition Y))))))}
      ( eq-is-contr
        ( is-contr-parity-transposition-permutation n X (transposition Y)))

module _
  {l l' : Level} (n : ℕ) (X : UU-Fin l n) (Y : UU-Fin l' n)
  where

  preserves-conjugation-sign-homomorphism-Fin-two :
    (f : (type-UU-Fin n X) ≃ (type-UU-Fin n X)) →
    (g : (type-UU-Fin n X) ≃ (type-UU-Fin n Y)) →
    Id ( sign-homomorphism-Fin-two n Y (g ∘e (f ∘e inv-equiv g)))
       ( sign-homomorphism-Fin-two n X f)
  preserves-conjugation-sign-homomorphism-Fin-two f g =
    apply-universal-property-trunc-Prop
      ( has-cardinality-type-UU-Fin n X)
      ( Id-Prop
        ( Fin-Set 2)
        ( sign-homomorphism-Fin-two n Y (g ∘e (f ∘e inv-equiv g)))
        ( sign-homomorphism-Fin-two n X f))
      ( λ h →
        ( ap
          ( pr1)
            ( eq-is-contr
              (is-contr-parity-transposition-permutation n Y (g ∘e (f ∘e inv-equiv g)))
              { x =
                center (is-contr-parity-transposition-permutation n Y (g ∘e (f ∘e inv-equiv g)))}
              { y =
                pair
                  ( mod-two-ℕ
                    ( length-list
                      ( map-list
                        ( map-equiv
                          ( equiv-universes-2-Element-Decidable-Subtype (type-UU-Fin n Y) l l'))
                        ( list-conjugation h))))
                  ( unit-trunc-Prop
                    ( pair
                      ( map-list
                        ( map-equiv
                          ( equiv-universes-2-Element-Decidable-Subtype (type-UU-Fin n Y) l l'))
                        ( list-conjugation h))
                      ( pair
                        ( refl)
                        ( ( inv
                          ( ( eq-htpy-equiv
                            ( correct-transposition-conjugation-equiv-list
                              ( type-UU-Fin n X)
                              ( type-UU-Fin n Y)
                              ( g)
                              ( list-trans h))) ∙
                            ( ap
                              ( λ h' → g ∘e (h' ∘e inv-equiv g))
                              ( eq-htpy-equiv
                                { e = permutation-list-transpositions (list-trans h)}
                                ( retr-permutation-list-transpositions-count
                                  ( type-UU-Fin n X)
                                  ( pair n h)
                                  ( f)))))) ∙
                          ( eq-equiv-universes-transposition-list
                            ( type-UU-Fin n Y)
                            ( l)
                            ( l')
                            ( list-conjugation h))))))})) ∙
          ( ( ap
            ( mod-two-ℕ)
            ( ( length-functor-list
              ( map-equiv
                ( equiv-universes-2-Element-Decidable-Subtype (type-UU-Fin n Y) l l'))
              ( list-conjugation h)) ∙
              ( length-functor-list
              ( transposition-conjugation-equiv (type-UU-Fin n X) (type-UU-Fin n Y) g)
              ( list-trans h)))) ∙
            ( ap
              ( pr1)
              { x =
                pair
                  ( mod-two-ℕ (length-list (list-trans h)))
                  ( unit-trunc-Prop
                    ( pair
                      ( list-trans h)
                      ( pair
                        ( refl)
                        ( inv
                          ( eq-htpy-equiv
                            ( retr-permutation-list-transpositions-count
                              ( type-UU-Fin n X)
                              ( pair n h)
                              ( f)))))))}
              { y = center (is-contr-parity-transposition-permutation n X f)}
              ( eq-is-contr
                ( is-contr-parity-transposition-permutation n X f)))))
    where
    list-trans :
      ( h : Fin n ≃ type-UU-Fin n X) →
      list
        ( Σ ( type-UU-Fin n X → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ
                  ( type-UU-Fin n X)
                  ( λ x → type-decidable-Prop (P x)))))
    list-trans h =
      list-transpositions-permutation-count
        ( type-UU-Fin n X)
        ( pair n h)
        ( f)
    list-conjugation :
      ( h : Fin n ≃ type-UU-Fin n X) →
      list
        ( Σ ( (type-UU-Fin n Y) → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ
                  ( type-UU-Fin n Y)
                  ( λ x → type-decidable-Prop (P x)))))
    list-conjugation h =
      map-list
        ( transposition-conjugation-equiv {l4 = l} (type-UU-Fin n X) (type-UU-Fin n Y) g)
        ( list-trans h)
```

### The sign homomorphism into the symmetric group S₂

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  map-sign-homomorphism : Aut (type-UU-Fin n X) → Aut (Fin 2)
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
      ( symmetric-Group (set-UU-Fin n X))
      ( symmetric-Group (Fin-Set 2))
  pr1 sign-homomorphism = map-sign-homomorphism
  pr2 sign-homomorphism = preserves-comp-map-sign-homomorphism

  eq-sign-homomorphism-transposition :
    ( Y : 2-Element-Decidable-Subtype l (type-UU-Fin n X)) →
    Id
      ( map-hom-Group
        ( symmetric-Group (set-UU-Fin n X))
        ( symmetric-Group (Fin-Set 2))
        ( sign-homomorphism)
        ( transposition Y))
      ( equiv-succ-Fin 2)
  eq-sign-homomorphism-transposition Y =
    ap aut-point-Fin-two-ℕ (eq-sign-homomorphism-Fin-two-transposition n X Y)

```
