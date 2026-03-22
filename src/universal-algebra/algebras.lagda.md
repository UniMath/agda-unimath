# Algebras of algebraic theories

```agda
module universal-algebra.algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.equivalences

open import lists.finite-sequences

open import universal-algebra.abstract-equations-over-signatures
open import universal-algebra.algebraic-theories
open import universal-algebra.equivalences-models-of-signatures
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

Given an [algebraic theory](universal-algebra.algebraic-theories.md), an
{{#concept "algebra" Disambiguation="of an algebraic theory, single-sorted, finitary" WD="algebraic structure" WDID=Q205464 Agda=Algebra}}
is a [model](universal-algebra.models-of-signatures.md) of a
[single-sorted finitary algebraic signature](universal-algebra.signatures.md) on
a [set](foundation-core.sets.md) that satisfies all
[equations](universal-algebra.abstract-equations-over-signatures.md) in the
theory.

## Definitions

### The predicate of being an algebra

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  satisfies-equation-prop-Model-Of-Signature :
    {l2 : Level} → abstract-equation σ → Model-Of-Signature l2 σ → Prop l2
  satisfies-equation-prop-Model-Of-Signature
    (k , lhs , rhs) (set-M , is-model-M) =
    Π-Prop
      ( fin-sequence (type-Set set-M) k)
      ( λ v →
        Id-Prop
          ( set-M)
          ( eval-term σ is-model-M v lhs)
          ( eval-term σ is-model-M v rhs))

module _
  {l1 l2 : Level} (σ : signature l1) (T : Algebraic-Theory l2 σ)
  where

  is-algebra-prop-Model-Of-Signature :
    {l3 : Level} → Model-Of-Signature l3 σ → Prop (l2 ⊔ l3)
  is-algebra-prop-Model-Of-Signature M =
    Π-Prop
      ( index-Algebraic-Theory σ T)
      ( λ e →
        satisfies-equation-prop-Model-Of-Signature
          ( σ)
          ( index-abstract-equation-Algebraic-Theory σ T e)
          ( M))

  is-algebra-Model-of-Signature :
    {l3 : Level} → Model-Of-Signature l3 σ → UU (l2 ⊔ l3)
  is-algebra-Model-of-Signature =
    is-in-subtype is-algebra-prop-Model-Of-Signature

  is-prop-is-algebra-Model-of-Signature :
    {l3 : Level} (M : Model-Of-Signature l3 σ) →
    is-prop (is-algebra-Model-of-Signature M)
  is-prop-is-algebra-Model-of-Signature =
    is-prop-is-in-subtype is-algebra-prop-Model-Of-Signature
```

### The type of algebras

```agda
Algebra :
  {l1 l2 : Level} (l3 : Level)
  (σ : signature l1) →
  Algebraic-Theory l2 σ →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
Algebra l3 σ T =
  type-subtype (is-algebra-prop-Model-Of-Signature σ T {l3})

module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (T : Algebraic-Theory l2 σ) (A : Algebra l3 σ T)
  where

  model-Algebra : Model-Of-Signature l3 σ
  model-Algebra = pr1 A

  set-Algebra : Set l3
  set-Algebra = set-Model-Of-Signature σ model-Algebra

  is-model-set-Algebra : is-model-of-signature σ set-Algebra
  is-model-set-Algebra = is-model-set-Model-Of-Signature σ model-Algebra

  type-Algebra : UU l3
  type-Algebra = type-Set set-Algebra

  is-set-type-Algebra : is-set type-Algebra
  is-set-type-Algebra = is-set-type-Set set-Algebra

  is-algebra-model-Algebra : is-algebra-Model-of-Signature σ T model-Algebra
  is-algebra-model-Algebra = pr2 A
```
