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
open import universal-algebra.equivalences-of-models-of-signatures
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

Given a [theory](universal-algebra.algebraic-theories.md), an
{{#concept "algebra" Disambiguation="of an algebraic theory" WD="algebraic structure" WDID=Q205464 Agda=Algebra}}
is a [model](universal-algebra.models-of-signatures.md) on a
[set](foundation-core.sets.md) such that it satisfies all
[equations](universal-algebra.abstract-equations-over-signatures.md) in the
theory.

## Definitions

### Algebra

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Theory σ l2)
  where

  is-algebra : {l3 : Level} → Model-Signature σ l3 → UU (l2 ⊔ l3)
  is-algebra M =
    (e : index-Theory σ T) →
    (assign : assignment σ (type-Model-Signature σ M)) →
    eval-term σ (is-model-set-Model-Signature σ M) assign
      ( lhs-abstract-equation σ (index-abstract-equation-Theory σ T e)) ＝
    eval-term σ (is-model-set-Model-Signature σ M) assign
      ( rhs-abstract-equation σ (index-abstract-equation-Theory σ T e))

  Algebra : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  Algebra l3 =
    Σ ( Model-Signature σ l3) (is-algebra)

module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (T : Theory σ l2) (A : Algebra σ T l3)
  where

  model-Algebra : Model-Signature σ l3
  model-Algebra = pr1 A

  set-Algebra : Set l3
  set-Algebra = set-Model-Signature σ model-Algebra

  is-model-set-Algebra : is-model σ set-Algebra
  is-model-set-Algebra = is-model-set-Model-Signature σ model-Algebra

  type-Algebra : UU l3
  type-Algebra = type-Set set-Algebra

  is-set-type-Algebra : is-set type-Algebra
  is-set-type-Algebra = is-set-type-Set set-Algebra

  is-algebra-Algebra : is-algebra σ T model-Algebra
  is-algebra-Algebra = pr2 A
```

## Properties

### Being an algebra is a proposition

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (T : Theory σ l2) (X : Model-Signature σ l3)
  where

  abstract
    is-prop-is-algebra : is-prop (is-algebra σ T X)
    is-prop-is-algebra =
      is-prop-Π
        ( λ e →
          ( is-prop-Π
            ( λ _ → is-set-type-Model-Signature σ X _ _)))

  is-algebra-Prop : Prop (l2 ⊔ l3)
  is-algebra-Prop = (is-algebra σ T X , is-prop-is-algebra)
```
