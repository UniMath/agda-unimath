# Algebras

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.algebras-of-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.equivalences

open import universal-algebra.abstract-equations-over-signatures
open import universal-algebra.algebraic-theories
open import universal-algebra.models-of-signatures
open import universal-algebra.equivalences-of-models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

Given a theory, an algebra is a model on a set such that it satisfies all
equations in the theory.

## Definitions

### Algebra

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Theory σ l2)
  where

  is-algebra : {l3 : Level} → Model-Signature σ l3 → UU (l2 ⊔ l3)
  is-algebra M =
    ( e : index-Theory σ T) →
    ( assign : assignment σ (type-Model-Signature σ M)) →
    eval-term σ (is-model-set-Model-Signature σ M) assign
      ( lhs-Abstract-Equation σ (index-Abstract-Equation-Theory σ T e)) ＝
      eval-term σ (is-model-set-Model-Signature σ M) assign
        ( rhs-Abstract-Equation σ (index-Abstract-Equation-Theory σ T e))

  Algebra : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  Algebra l3 =
    Σ ( Model-Signature σ l3) (is-algebra)

  model-Algebra :
    {l3 : Level} →
    Algebra l3 → Model-Signature σ l3
  model-Algebra A = pr1 A

  set-Algebra :
    {l3 : Level} →
    Algebra l3 → Set l3
  set-Algebra A = pr1 (pr1 A)

  is-model-set-Algebra :
    {l3 : Level} →
    (A : Algebra l3) →
    is-model-signature σ (set-Algebra A)
  is-model-set-Algebra A = pr2 (pr1 A)

  type-Algebra :
    {l3 : Level} →
    Algebra l3 → UU l3
  type-Algebra A =
    pr1 (pr1 (pr1 A))

  is-set-type-Algebra :
    {l3 : Level} →
    (A : Algebra l3) → is-set (type-Algebra A)
  is-set-type-Algebra A = pr2 (pr1 (pr1 A))

  is-algebra-Algebra :
    {l3 : Level} →
    (A : Algebra l3) →
    is-algebra (model-Algebra A)
  is-algebra-Algebra A = pr2 A
```

## Properties

### Being an algebra is a proposition

```agda
  is-prop-is-algebra :
    {l3 : Level} →
    (X : Model-Signature σ l3) →
    is-prop (is-algebra X)
  is-prop-is-algebra M =
    is-prop-Π
      ( λ e →
        ( is-prop-Π
          ( λ assign → is-set-type-Model-Signature σ M _ _)))

  is-algebra-Prop :
    {l3 : Level} (X : Model-Signature σ l3) → Prop (l2 ⊔ l3)
  pr1 (is-algebra-Prop X) = is-algebra X
  pr2 (is-algebra-Prop X) = is-prop-is-algebra X
```

### Characterizing identifications of algebras

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Theory σ l2)
  where

  Eq-Algebra : {l3 : Level} (A B : Algebra σ T l3) → UU (l1 ⊔ l3)
  Eq-Algebra A B =
    Eq-Model-Signature σ (model-Algebra σ T A) (model-Algebra σ T B)

  Eq-eq-Algebra :
    {l3 : Level} (A B : Algebra σ T l3) → A ＝ B → Eq-Algebra A B
  Eq-eq-Algebra A .A refl = refl-Eq-Model-Signature σ (model-Algebra σ T A)

  is-equiv-Eq-eq-Algebra :
    {l3 : Level} (A B : Algebra σ T l3) →
    is-equiv (Eq-eq-Algebra A B)
  is-equiv-Eq-eq-Algebra (A , p) =
    subtype-identity-principle
      ( is-prop-is-algebra σ T)
      ( p)
      ( refl-Eq-Model-Signature σ A)
      ( Eq-eq-Algebra (A , p))
      ( is-equiv-Eq-eq-Model-Signature σ A)

  equiv-Eq-eq-Algebra :
    {l3 : Level} (A B : Algebra σ T l3) →
    (A ＝ B) ≃ Eq-Algebra A B
  pr1 (equiv-Eq-eq-Algebra A B) = Eq-eq-Algebra A B
  pr2 (equiv-Eq-eq-Algebra A B) = is-equiv-Eq-eq-Algebra A B

  eq-Eq-Algebra :
    {l3 : Level} (A B : Algebra σ T l3) →
    Eq-Algebra A B → A ＝ B
  eq-Eq-Algebra A B = map-inv-equiv (equiv-Eq-eq-Algebra A B)

  abstract
    is-torsorial-Eq-Algebra :
      {l3 : Level} (A : Algebra σ T l3) → is-torsorial (Eq-Algebra A)
    is-torsorial-Eq-Algebra A =
      fundamental-theorem-id'
        ( Eq-eq-Algebra A)
        ( λ B → is-equiv-Eq-eq-Algebra A B)
```
