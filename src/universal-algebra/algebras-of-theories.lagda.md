# Algebras

```agda
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
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  where

  is-algebra :
    { l3 : Level} →
    ( X : Model-Signature Sg l3) → UU (l2 ⊔ l3)
  is-algebra M =
    ( e : index-Theory Sg Th) →
    ( assign : assignment Sg (type-Model-Signature Sg M)) →
    eval-term Sg (is-model-set-Model-Signature Sg M) assign
      ( lhs-Abstract-Equation Sg (index-Abstract-Equation-Theory Sg Th e)) ＝
      eval-term Sg (is-model-set-Model-Signature Sg M) assign
        ( rhs-Abstract-Equation Sg (index-Abstract-Equation-Theory Sg Th e))

  Algebra :
    ( l3 : Level) →
    UU (l1 ⊔ l2 ⊔ lsuc l3)
  Algebra l3 =
    Σ ( Model-Signature Sg l3) (is-algebra)

  model-Algebra :
    { l3 : Level} →
    Algebra l3 → Model-Signature Sg l3
  model-Algebra Alg = pr1 Alg

  set-Algebra :
    { l3 : Level} →
    Algebra l3 → Set l3
  set-Algebra Alg = pr1 (pr1 Alg)

  is-model-set-Algebra :
    { l3 : Level} →
    ( Alg : Algebra l3) →
    is-model-signature Sg (set-Algebra Alg)
  is-model-set-Algebra Alg = pr2 (pr1 Alg)

  type-Algebra :
    { l3 : Level} →
    Algebra l3 → UU l3
  type-Algebra Alg =
    pr1 (pr1 (pr1 Alg))

  is-set-Algebra :
    { l3 : Level} →
    (Alg : Algebra l3) → is-set (type-Algebra Alg)
  is-set-Algebra Alg = pr2 (pr1 (pr1 Alg))

  is-algebra-Algebra :
    { l3 : Level} →
    ( Alg : Algebra l3) →
    is-algebra (model-Algebra Alg)
  is-algebra-Algebra Alg = pr2 Alg
```

## Properties

### Being an algebra is a proposition

```agda
  is-prop-is-algebra :
    { l3 : Level} →
    ( X : Model-Signature Sg l3) →
    is-prop (is-algebra X)
  is-prop-is-algebra M =
    is-prop-Π
      ( λ e →
        ( is-prop-Π
          ( λ assign → is-set-type-Model-Signature Sg M _ _)))

  is-algebra-Prop :
    {l3 : Level} (X : Model-Signature Sg l3) → Prop (l2 ⊔ l3)
  pr1 (is-algebra-Prop X) = is-algebra X
  pr2 (is-algebra-Prop X) = is-prop-is-algebra X
```

### Characterizing identifications of algebras

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  where

  Eq-Algebra : {l3 : Level} (A B : Algebra Sg Th l3) → UU (l1 ⊔ l3)
  Eq-Algebra A B =
    Eq-Model-Signature Sg (model-Algebra Sg Th A) (model-Algebra Sg Th B)

  Eq-eq-Algebra :
    {l3 : Level} (A B : Algebra Sg Th l3) → A ＝ B →
    Eq-Algebra A B
  Eq-eq-Algebra A .A refl = refl-Eq-Model-Signature Sg (model-Algebra Sg Th A)

  is-equiv-Eq-eq-Algebra :
    {l3 : Level} (A B : Algebra Sg Th l3) →
    is-equiv (Eq-eq-Algebra A B)
  is-equiv-Eq-eq-Algebra (A , p) =
    subtype-identity-principle
    ( is-prop-is-algebra Sg Th)
    ( p)
    ( refl-Eq-Model-Signature Sg A)
    ( Eq-eq-Algebra (A , p))
    ( is-equiv-Eq-eq-Model-Signature Sg A)

  is-torsorial-Eq-Algebra :
    {l3 : Level} (A : Algebra Sg Th l3) → is-torsorial (Eq-Algebra A)
  is-torsorial-Eq-Algebra A =
    fundamental-theorem-id'
    ( Eq-eq-Algebra A)
    ( λ B → is-equiv-Eq-eq-Algebra A B)
```
