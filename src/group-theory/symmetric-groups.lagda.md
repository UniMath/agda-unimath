# Symmetric groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.symmetric-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using
  (eq-pair-Σ; pair-eq-Σ; comp-eq-pair-Σ; comp-pair-eq-Σ; issec-pair-eq-Σ; isretr-pair-eq-Σ)
open import foundation.equivalences using
  ( _∘e_; associative-comp-equiv; id-equiv; left-unit-law-equiv; inv-equiv;
    right-unit-law-equiv; left-inverse-law-equiv; right-inverse-law-equiv;
    distributive-inv-comp-equiv; inv-inv-equiv; map-equiv; eq-htpy-equiv)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using
  (Id; refl; _∙_; ap; inv; ap-binary)
open import foundation.propositional-truncations using
  (type-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.raising-universe-levels using (raise-Set; equiv-raise)
open import foundation.sets using
  ( UU-Set; type-Set; is-set; is-set-type-Set; aut-Set; is-prop-is-set)
open import foundation.subuniverses using (is-one-type-UU-Set)
open import foundation.truncated-types using (is-trunc-Id)
open import foundation.univalence using
  ( equiv-eq; eq-equiv; comp-eq-equiv; comp-equiv-eq; equiv-univalence)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.automorphism-groups using (Automorphism-Group)
open import group-theory.concrete-groups using (abstract-group-Concrete-Group)
open import group-theory.groups using (is-group'; Group; semigroup-Group)
open import group-theory.homomorphisms-groups using (id-hom-Group)
open import group-theory.homomorphisms-semigroups using (is-prop-preserves-mul-Semigroup)
open import group-theory.isomorphisms-groups using (type-iso-Group)
open import group-theory.monoids using (is-unital)
open import group-theory.semigroups using (has-associative-mul-Set; Semigroup)
```

## Definitions

```agda
set-symmetric-Group : {l : Level} (X : UU-Set l) → UU-Set l
set-symmetric-Group X = aut-Set X

type-symmetric-Group : {l : Level} (X : UU-Set l) → UU l
type-symmetric-Group X = type-Set (set-symmetric-Group X)

is-set-type-symmetric-Group :
  {l : Level} (X : UU-Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group X = is-set-type-Set (set-symmetric-Group X)

has-associative-mul-aut-Set :
  {l : Level} (X : UU-Set l) → has-associative-mul-Set (aut-Set X)
pr1 (has-associative-mul-aut-Set X) f e = f ∘e e
pr2 (has-associative-mul-aut-Set X) e f g = associative-comp-equiv g f e

symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → Semigroup l
pr1 (symmetric-Semigroup X) = set-symmetric-Group X
pr2 (symmetric-Semigroup X) = has-associative-mul-aut-Set X

is-unital-symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → is-unital (symmetric-Semigroup X)
pr1 (is-unital-symmetric-Semigroup X) = id-equiv
pr1 (pr2 (is-unital-symmetric-Semigroup X)) = left-unit-law-equiv
pr2 (pr2 (is-unital-symmetric-Semigroup X)) = right-unit-law-equiv

is-group-symmetric-Semigroup' :
  {l : Level} (X : UU-Set l) →
  is-group' (symmetric-Semigroup X) (is-unital-symmetric-Semigroup X)
pr1 (is-group-symmetric-Semigroup' X) = inv-equiv
pr1 (pr2 (is-group-symmetric-Semigroup' X)) = left-inverse-law-equiv
pr2 (pr2 (is-group-symmetric-Semigroup' X)) = right-inverse-law-equiv

symmetric-Group :
  {l : Level} → UU-Set l → Group l
pr1 (symmetric-Group X) = symmetric-Semigroup X
pr1 (pr2 (symmetric-Group X)) = is-unital-symmetric-Semigroup X
pr2 (pr2 (symmetric-Group X)) = is-group-symmetric-Semigroup' X
```

## Properties

```agda
module _
  {l1 l2 : Level}
  where
  
  iso-Symmetric-Group-abstract-Automorphism-Group : (X : UU-Set l1) →
    type-iso-Group
      ( symmetric-Group X)
      ( abstract-group-Concrete-Group
        ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) (is-one-type-UU-Set (l1 ⊔ l2))))
  pr1 (pr1 (iso-Symmetric-Group-abstract-Automorphism-Group X)) x =
    eq-pair-Σ
      ( eq-pair-Σ
        ( eq-equiv
          ( type-Set (raise-Set l2 X))
          ( type-Set (raise-Set l2 X))
          ( equiv-raise l2 (type-Set X) ∘e
            ( (inv-equiv x) ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
        ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
      ( eq-is-prop is-prop-type-trunc-Prop) 
  pr2 (pr1 (iso-Symmetric-Group-abstract-Automorphism-Group X)) x y =
    ( ap
      ( λ P → eq-pair-Σ P (eq-is-prop is-prop-type-trunc-Prop))
      ( ap
        ( λ Q → eq-pair-Σ Q (eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
        ( ( ap
          ( eq-equiv (type-Set (raise-Set l2 X)) (type-Set (raise-Set l2 X)))
          ( ( ap
            ( λ e → equiv-raise l2 (type-Set X) ∘e (e ∘e inv-equiv (equiv-raise l2 (type-Set X))))
            ( distributive-inv-comp-equiv y x ∙
              (eq-htpy-equiv refl-htpy ∙
                ( ap
                  ( λ e → inv-equiv y ∘e (e ∘e inv-equiv x))
                  ( inv (left-inverse-law-equiv (equiv-raise l2 (type-Set X)))))))) ∙
            ( eq-htpy-equiv refl-htpy))) ∙
          ( inv
            ( comp-eq-equiv
              ( type-Set (raise-Set l2 X))
              ( type-Set (raise-Set l2 X))
              ( type-Set (raise-Set l2 X))
              ( equiv-raise l2 (type-Set X) ∘e (inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X))))
              ( equiv-raise l2 (type-Set X) ∘e (inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X))))))) ∙
        ( ( ap
          ( λ w →
            eq-pair-Σ
              ( ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e (inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X))))) ∙
                ( eq-equiv
                  ( type-Set (raise-Set l2 X))
                  ( type-Set (raise-Set l2 X))
                  ( equiv-raise l2 (type-Set X) ∘e
                    ( inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X))))))
              ( w))
          ( eq-is-prop (is-trunc-Id (is-prop-is-set (type-Set (raise-Set l2 X)) _ _)))) ∙
          ( inv
            ( comp-eq-pair-Σ
              ( pr2 (raise-Set l2 X))
              ( pr2 (raise-Set l2 X))
              ( pr2 (raise-Set l2 X))
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  ( inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))))))) ∙
      ( ap
        ( λ w →
          eq-pair-Σ
            ( ( eq-pair-Σ
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))) ∙
               eq-pair-Σ
                ( eq-equiv
                  (type-Set (raise-Set l2 X))
                  (type-Set (raise-Set l2 X))
                  ( equiv-raise l2 (type-Set X) ∘e
                    (inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
            ( w))
        ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ (unit-trunc-Prop refl)))) ∙
         inv
          ( comp-eq-pair-Σ
            ( unit-trunc-Prop refl)
            ( unit-trunc-Prop refl)
            ( unit-trunc-Prop refl)
            ( eq-pair-Σ
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  (inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
            ( eq-pair-Σ
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  (inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
            ( eq-is-prop is-prop-type-trunc-Prop)
            ( eq-is-prop is-prop-type-trunc-Prop))) 
  pr1 (pr1 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) x =
    inv-equiv
      ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
        ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X)))
  pr2 (pr1 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) x y =
    ( ap
      ( inv-equiv)
      { y =
        ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))) ∘e equiv-raise l2 (type-Set X))) ∘e
          ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
            ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X)))}
      ( ( ap
        ( λ e → inv-equiv (equiv-raise l2 (type-Set X)) ∘e (e ∘e equiv-raise l2 (type-Set X)))
        ( ( ap
          ( equiv-eq)
          ( ( ap (λ p → pr1 (pair-eq-Σ p)) (inv (comp-pair-eq-Σ x y))) ∙
            ( inv (comp-pair-eq-Σ (pr1 (pair-eq-Σ x)) (pr1 (pair-eq-Σ y)))))) ∙
          ( ( inv
            ( comp-equiv-eq
              ( pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x))))
              ( pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))))) ∙
            ( ( eq-htpy-equiv refl-htpy) ∙
              ( ap
                ( λ e →
                  equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))) ∘e
                    (e ∘e equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x))))))
                ( inv (right-inverse-law-equiv (equiv-raise l2 (type-Set X))))))))) ∙
        ( eq-htpy-equiv refl-htpy))) ∙
      ( distributive-inv-comp-equiv
        ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X)))
        ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))) ∘e equiv-raise l2 (type-Set X))))
  pr1 (pr2 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) =
    eq-pair-Σ
      ( eq-htpy
        ( λ x →
          (  ap
            ( λ w →
              eq-pair-Σ
                ( w)
                ( eq-is-prop is-prop-type-trunc-Prop))
            ( ( ap
              (λ w →
                eq-pair-Σ w (eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
              ( ( ap
                ( eq-equiv (type-Set (raise-Set l2 X)) (type-Set (raise-Set l2 X)))
                ( ( ap
                  ( λ e → equiv-raise l2 (type-Set X) ∘e (e ∘e inv-equiv (equiv-raise l2 (type-Set X))))
                  ( inv-inv-equiv
                    ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
                      (equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X))))) ∙
                  ( ( eq-htpy-equiv refl-htpy) ∙
                    ( ( ap
                      ( λ e →
                        e ∘e
                          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e
                            ( equiv-raise l2 (type-Set X) ∘e
                              inv-equiv (equiv-raise l2 (type-Set X)))))
                      ( right-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                      ( ( ap
                        ( λ e → id-equiv ∘e (equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e e))
                        ( right-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                        ( eq-htpy-equiv refl-htpy)))))) ∙
                ( ap
                  ( λ e → map-equiv e (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))))
                  ( left-inverse-law-equiv equiv-univalence)))) ∙
              ( ( ap
                ( eq-pair-Σ (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))))
                { y = pr2 (pair-eq-Σ (pr1 (pair-eq-Σ x)))}
                ( eq-is-prop (is-trunc-Id (is-prop-is-set (type-Set (raise-Set l2 X)) _ _)))) ∙
                ( issec-pair-eq-Σ (raise-Set l2 X) (raise-Set l2 X) (pr1 (pair-eq-Σ x))))) ∙
            ( ( ap
              ( eq-pair-Σ (pr1 (pair-eq-Σ x)))
              { y = pr2 (pair-eq-Σ x)}
              ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
              ( issec-pair-eq-Σ
                ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                ( x))))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group
            ( abstract-group-Concrete-Group
              ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) (is-one-type-UU-Set (l1 ⊔ l2)))))
          ( semigroup-Group
            ( abstract-group-Concrete-Group
              ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) (is-one-type-UU-Set (l1 ⊔ l2)))))
          ( pr1
            ( id-hom-Group
              ( abstract-group-Concrete-Group
                ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) (is-one-type-UU-Set (l1 ⊔ l2))))))))
  pr2 (pr2 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) =
    eq-pair-Σ
      ( eq-htpy
        ( λ x →
          ( ap
            ( inv-equiv)
            { y = inv-equiv x}
            ( ( ap
              ( λ e →
                ( inv-equiv (equiv-raise l2 (type-Set X))) ∘e
                  ( e ∘e equiv-raise l2 (type-Set X)))
              ( ( ap
                ( equiv-eq)
                ( ap
                  ( λ w → pr1 (pair-eq-Σ w))
                  ( ap pr1
                    ( isretr-pair-eq-Σ
                      ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                      ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                      ( pair
                        ( eq-pair-Σ
                          ( eq-equiv
                            ( type-Set (raise-Set l2 X))
                            ( type-Set (raise-Set l2 X))
                            ( equiv-raise l2 (type-Set X) ∘e
                              ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                          ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
                        ( eq-is-prop is-prop-type-trunc-Prop)))) ∙
                    ( ap pr1
                      ( isretr-pair-eq-Σ (raise-Set l2 X) (raise-Set l2 X)
                        ( pair
                          ( eq-equiv
                            ( type-Set (raise-Set l2 X))
                            ( type-Set (raise-Set l2 X))
                            ( equiv-raise l2 (type-Set X) ∘e
                              ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                          ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))))))) ∙
                ( ap
                  ( λ e →
                    map-equiv
                      ( e)
                      ( equiv-raise l2 (type-Set X) ∘e
                        ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                  ( right-inverse-law-equiv equiv-univalence)))) ∙
              ( eq-htpy-equiv refl-htpy ∙
                ( ( ap
                  ( λ e →
                    e ∘e
                      (inv-equiv x ∘e
                        (inv-equiv (equiv-raise l2 (type-Set X)) ∘e
                          equiv-raise l2 (type-Set X))))
                   ( left-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                   ( ( ap
                     ( λ e → id-equiv ∘e (inv-equiv x ∘e e))
                     ( left-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                     ( eq-htpy-equiv refl-htpy)))))) ∙
            ( inv-inv-equiv x)))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (symmetric-Group X))
          ( semigroup-Group (symmetric-Group X))
          ( pr1 (id-hom-Group (symmetric-Group X)))))
```
