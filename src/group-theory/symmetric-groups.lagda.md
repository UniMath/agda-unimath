# Symmetric groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.symmetric-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using
  (eq-pair-Σ; pair-eq-Σ; comp-eq-pair-Σ; comp-pair-eq-Σ)
open import foundation.equivalences using
  ( _∘e_; associative-comp-equiv; id-equiv; left-unit-law-equiv; inv-equiv;
    right-unit-law-equiv; left-inverse-law-equiv; right-inverse-law-equiv;
    distributive-inv-comp-equiv)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.identity-types using (Id; refl; _∙_; ap; inv)
open import foundation.propositional-truncations using
  (type-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.sets using
  ( UU-Set; type-Set; is-set; is-set-type-Set; aut-Set; is-prop-is-set)
open import foundation.subuniverses using (is-one-type-UU-Set)
open import foundation.truncated-types using (is-trunc-Id)
open import foundation.univalence using
  ( equiv-eq; eq-equiv; comp-eq-equiv; comp-equiv-eq)
open import foundation.universe-levels using (Level; UU)

open import group-theory.automorphism-groups using (Automorphism-Group)
open import group-theory.concrete-groups using (abstract-group-Concrete-Group)
open import group-theory.groups using (is-group'; Group)
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
iso-Symmetric-Group-abstract-Automorphism-Group : {l : Level} (X : UU-Set l) →
  type-iso-Group
    ( symmetric-Group X)
    ( abstract-group-Concrete-Group
      ( Automorphism-Group (UU-Set l) X (is-one-type-UU-Set l)))
pr1 (pr1 (iso-Symmetric-Group-abstract-Automorphism-Group X)) x =
  eq-pair-Σ
    ( eq-pair-Σ
      ( eq-equiv (type-Set X) (type-Set X) (inv-equiv x))
      ( eq-is-prop (is-prop-is-set (type-Set X))))
    ( eq-is-prop is-prop-type-trunc-Prop)
pr2 (pr1 (iso-Symmetric-Group-abstract-Automorphism-Group X)) x y =
    ap
    ( λ P → eq-pair-Σ P (eq-is-prop is-prop-type-trunc-Prop))
    (  ap
      ( λ Q → eq-pair-Σ Q (eq-is-prop (is-prop-is-set (type-Set X))))
      ( ( ap
        ( eq-equiv (type-Set X) (type-Set X))
        ( distributive-inv-comp-equiv y x)) ∙
        ( inv
          ( comp-eq-equiv (type-Set X) (type-Set X) (type-Set X)
            ( inv-equiv x) (inv-equiv y)))) ∙
      ( ( ap
        ( λ w →
          eq-pair-Σ
            ( eq-equiv (pr1 X) (pr1 X) (inv-equiv x) ∙ eq-equiv (pr1 X) (pr1 X) (inv-equiv y))
            ( w))
        ( eq-is-prop (is-trunc-Id (is-prop-is-set (pr1 X) _ (pr2 X))))) ∙
        ( inv
          ( comp-eq-pair-Σ (pr2 X) (pr2 X) (pr2 X)
            ( eq-equiv (pr1 X) (pr1 X) (inv-equiv x))
            ( eq-equiv (pr1 X) (pr1 X) (inv-equiv y))
            ( eq-is-prop (is-prop-is-set (pr1 X)))
            ( eq-is-prop (is-prop-is-set (pr1 X))))))) ∙
    ( ap
      ( λ w →
        eq-pair-Σ
          ( ( eq-pair-Σ
            ( eq-equiv (pr1 X) (pr1 X) (inv-equiv x))
            ( eq-is-prop (is-prop-is-set (pr1 X)))) ∙
            ( eq-pair-Σ
              (eq-equiv (pr1 X) (pr1 X) (inv-equiv y))
              ( eq-is-prop (is-prop-is-set (pr1 X)))))
          ( w))
      ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ (unit-trunc-Prop refl)))) ∙
      ( inv
        ( comp-eq-pair-Σ
          ( unit-trunc-Prop refl)
          ( unit-trunc-Prop refl)
          ( unit-trunc-Prop refl)
          ( eq-pair-Σ
            ( eq-equiv (type-Set X) (type-Set X) (inv-equiv x))
            ( eq-is-prop (is-prop-is-set (type-Set X))))
          ( eq-pair-Σ
            ( eq-equiv (type-Set X) (type-Set X) (inv-equiv y))
            ( eq-is-prop (is-prop-is-set (type-Set X))))
          ( eq-is-prop is-prop-type-trunc-Prop)
          ( eq-is-prop is-prop-type-trunc-Prop))))
pr1 (pr1 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) x =
  inv-equiv (equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))))
pr2 (pr1 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) x y =
  ( ap
    ( inv-equiv)
    ( ap
      ( equiv-eq)
      ( (ap
        ( λ p → pr1 (pair-eq-Σ p))
        ( inv (comp-pair-eq-Σ x y))) ∙
        ( inv (comp-pair-eq-Σ (pr1 (pair-eq-Σ x)) (pr1 (pair-eq-Σ y))))) ∙
      ( inv
        ( comp-equiv-eq
          ( pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x))))
          ( pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))))))) ∙
    ( distributive-inv-comp-equiv
      ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))))
      ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y))))))
pr1 (pr2 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) =
  eq-pair-Σ
    ( eq-htpy
      (λ x → {!ap-binary !}))
    ( eq-is-prop
      ( is-prop-preserves-mul-Semigroup {!!} {!!} {!!}))
pr2 (pr2 (pr2 (iso-Symmetric-Group-abstract-Automorphism-Group X))) = {!!}
```
