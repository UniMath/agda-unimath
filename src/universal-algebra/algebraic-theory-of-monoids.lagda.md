# The algebraic theory of monoids

```agda
module universal-algebra.algebraic-theory-of-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.sets
open import foundation.subtypes
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-semigroups
open import universal-algebra.algebras
open import universal-algebra.extensions-signatures
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
open import universal-algebra.abstract-equations-over-signatures
```

</details>

## Idea

There is an
{{#concept "algebraic theory of monoids" Agda=algebraic-theory-Monoid}}. The
type of all such [algebras](universal-algebra.algebras.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[monoids](group-theory.monoids.md).

## Definition

```agda
data operation-Monoid : UU lzero where
  operation-monoid-operation-Semigroup : operation-Semigroup → operation-Monoid
  unit-operation-Monoid : operation-Monoid

pattern mul-operation-Monoid =
  operation-monoid-operation-Semigroup mul-operation-Semigroup

signature-Monoid : signature lzero
pr1 signature-Monoid = operation-Monoid
pr2 signature-Monoid (operation-monoid-operation-Semigroup op) =
  arity-operation-signature signature-Semigroup op
pr2 signature-Monoid unit-operation-Monoid = 0

data law-Monoid : UU lzero where
  law-monoid-law-Semigroup : law-Semigroup → law-Monoid
  left-unit-mul-law-Monoid : law-Monoid
  right-unit-mul-law-Monoid : law-Monoid

pattern associative-mul-law-Monoid =
  law-monoid-law-Semigroup associative-mul-law-Semigroup

extension-signature-semigroup-Monoid :
  is-extension-of-signature signature-Semigroup signature-Monoid
pr1 extension-signature-semigroup-Monoid =
  operation-monoid-operation-Semigroup
pr2 extension-signature-semigroup-Monoid _ = refl

algebraic-theory-Monoid : Algebraic-Theory lzero signature-Monoid
pr1 algebraic-theory-Monoid = law-Monoid
pr2 algebraic-theory-Monoid =
  let
    var : (i k : ℕ) → term signature-Monoid (succ-ℕ k)
    var i k = var-term (mod-succ-ℕ k i)
    _*-term_ :
      {k : ℕ} →
      term signature-Monoid k → term signature-Monoid k →
      term signature-Monoid k
    _*-term_ x y = op-term mul-operation-Monoid (x ∷ y ∷ empty-tuple)
    unit-term = op-term unit-operation-Monoid empty-tuple
  in
    λ where
      (law-monoid-law-Semigroup law) →
        translation-abstract-equation
          ( signature-Semigroup)
          ( signature-Monoid)
          ( extension-signature-semigroup-Monoid)
          ( index-abstract-equation-Algebraic-Theory
            ( signature-Semigroup)
            ( algebraic-theory-Semigroup)
            ( law))
      left-unit-mul-law-Monoid →
        ( 1 ,
          unit-term *-term var 0 0 ,
          var 0 0)
      right-unit-mul-law-Monoid →
        ( 1 ,
          var 0 0 *-term unit-term ,
          var 0 0)

Algebra-Monoid : (l : Level) → UU (lsuc l)
Algebra-Monoid l =
  Algebra l signature-Monoid algebraic-theory-Monoid
```

## Properties

### Algebras in the theory of monoids from monoids

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  algebra-semigroup-Monoid : Algebra-Semigroup l
  algebra-semigroup-Monoid =
    algebra-semigroup-Semigroup (semigroup-Monoid M)

  is-model-set-Monoid : is-model-of-signature signature-Monoid (set-Monoid M)
  is-model-set-Monoid (operation-monoid-operation-Semigroup op) =
    is-model-set-Algebra
      ( signature-Semigroup)
      ( algebraic-theory-Semigroup)
      ( algebra-semigroup-Monoid)
      ( op)
  is-model-set-Monoid unit-operation-Monoid empty-tuple = unit-Monoid M

  model-set-Monoid : Model-Of-Signature l signature-Monoid
  model-set-Monoid =
    ( set-Monoid M ,
      is-model-set-Monoid)

  is-algebra-model-set-Monoid :
    is-algebra-Model-of-Signature
      ( signature-Monoid)
      ( algebraic-theory-Monoid)
      ( model-set-Monoid)
  is-algebra-model-set-Monoid associative-mul-law-Monoid _ =
    associative-mul-Monoid M _ _ _
  is-algebra-model-set-Monoid left-unit-mul-law-Monoid _ =
    left-unit-law-mul-Monoid M _
  is-algebra-model-set-Monoid right-unit-mul-law-Monoid _ =
    right-unit-law-mul-Monoid M _

  algebra-monoid-Monoid : Algebra-Monoid l
  algebra-monoid-Monoid =
    ( model-set-Monoid ,
      is-algebra-model-set-Monoid)
```

### Monoids from algebras in the theory of monoids

```agda
module _
  {l : Level}
  (A@((set-A , model-A) , satisfies-A) : Algebra-Monoid l)
  where

  algebra-semigroup-Algebra-Monoid : Algebra-Semigroup l
  algebra-semigroup-Algebra-Monoid =
    ( ( set-A ,
        model-A ∘ operation-monoid-operation-Semigroup) ,
      λ where
        associative-mul-law-Semigroup → satisfies-A associative-mul-law-Monoid)

  semigroup-Algebra-Monoid : Semigroup l
  semigroup-Algebra-Monoid =
    semigroup-Algebra-Semigroup algebra-semigroup-Algebra-Monoid

  type-Algebra-Monoid : UU l
  type-Algebra-Monoid = type-Set set-A

  mul-Algebra-Monoid :
    type-Algebra-Monoid → type-Algebra-Monoid → type-Algebra-Monoid
  mul-Algebra-Monoid = mul-Semigroup semigroup-Algebra-Monoid

  unit-Algebra-Monoid : type-Algebra-Monoid
  unit-Algebra-Monoid = model-A unit-operation-Monoid empty-tuple

  left-unit-law-mul-Algebra-Monoid :
    left-unit-law mul-Algebra-Monoid unit-Algebra-Monoid
  left-unit-law-mul-Algebra-Monoid x =
    satisfies-A left-unit-mul-law-Monoid (λ _ → x)

  right-unit-law-mul-Algebra-Monoid :
    right-unit-law mul-Algebra-Monoid unit-Algebra-Monoid
  right-unit-law-mul-Algebra-Monoid x =
    satisfies-A right-unit-mul-law-Monoid (λ _ → x)

  monoid-Algebra-Monoid : Monoid l
  monoid-Algebra-Monoid =
    ( semigroup-Algebra-Monoid ,
      unit-Algebra-Monoid ,
      left-unit-law-mul-Algebra-Monoid ,
      right-unit-law-mul-Algebra-Monoid)
```

### The type of monoids is equivalent to the type of algebras in the theory of monoids

```agda
abstract
  is-section-monoid-Algebra-Monoid :
    {l : Level} (A : Algebra-Monoid l) →
    algebra-monoid-Monoid (monoid-Algebra-Monoid A) ＝ A
  is-section-monoid-Algebra-Monoid ((set-A , model-A) , satisfies-A) =
    eq-type-subtype
      ( is-algebra-prop-Model-Of-Signature
        ( signature-Monoid)
        ( algebraic-theory-Monoid))
      ( eq-pair-eq-fiber
        ( eq-binary-htpy _ _
          ( λ where
            mul-operation-Monoid (x ∷ y ∷ empty-tuple) → refl
            unit-operation-Monoid empty-tuple → refl)))

  is-retraction-monoid-Algebra-Monoid :
    {l : Level} (M : Monoid l) →
    monoid-Algebra-Monoid (algebra-monoid-Monoid M) ＝ M
  is-retraction-monoid-Algebra-Monoid _ = refl

is-equiv-algebra-monoid-Monoid :
  {l : Level} → is-equiv (algebra-monoid-Monoid {l})
is-equiv-algebra-monoid-Monoid =
  is-equiv-is-invertible
    ( monoid-Algebra-Monoid)
    ( is-section-monoid-Algebra-Monoid)
    ( is-retraction-monoid-Algebra-Monoid)

equiv-algebra-monoid-Monoid :
  {l : Level} → Monoid l ≃ Algebra-Monoid l
equiv-algebra-monoid-Monoid =
  ( algebra-monoid-Monoid ,
    is-equiv-algebra-monoid-Monoid)
```

### Homomorphisms of monoids are equivalent to homomorphisms in the algebra of monoids

```agda
hom-Algebra-Monoid :
  {l1 l2 : Level} → Algebra-Monoid l1 → Algebra-Monoid l2 → UU (l1 ⊔ l2)
hom-Algebra-Monoid =
  hom-Algebra signature-Monoid algebraic-theory-Monoid

hom-monoid-hom-Algebra-Monoid :
  {l1 l2 : Level} (M : Algebra-Monoid l1) (N : Algebra-Monoid l2) →
  hom-Algebra-Monoid M N →
  hom-Monoid (monoid-Algebra-Monoid M) (monoid-Algebra-Monoid N)
hom-monoid-hom-Algebra-Monoid M N (f , preserves-ops-f) =
  ( (f , preserves-ops-f mul-operation-Monoid (_ ∷ _ ∷ empty-tuple)) ,
    preserves-ops-f unit-operation-Monoid empty-tuple)

module _
  {l1 l2 : Level}
  (M : Monoid l1)
  (N : Monoid l2)
  where

  hom-algebra-monoid-hom-Monoid :
    hom-Monoid M N →
    hom-Algebra-Monoid (algebra-monoid-Monoid M) (algebra-monoid-Monoid N)
  hom-algebra-monoid-hom-Monoid
    ((f , preserves-mul-f) , preserves-unit-f) =
    ( f ,
      λ where
        mul-operation-Monoid (x ∷ y ∷ empty-tuple) → preserves-mul-f
        unit-operation-Monoid empty-tuple → preserves-unit-f)

  is-equiv-hom-algebra-monoid-hom-Monoid :
    is-equiv hom-algebra-monoid-hom-Monoid
  is-equiv-hom-algebra-monoid-hom-Monoid =
    is-equiv-is-invertible
      ( hom-monoid-hom-Algebra-Monoid
        ( algebra-monoid-Monoid M)
        ( algebra-monoid-Monoid N))
      ( λ φ →
        eq-htpy-hom-Algebra
          ( signature-Monoid)
          ( algebraic-theory-Monoid)
          ( algebra-monoid-Monoid M)
          ( algebra-monoid-Monoid N)
          ( _)
          ( φ)
          ( refl-htpy))
      ( λ φ → eq-htpy-hom-Monoid M N _ φ refl-htpy)

  equiv-hom-algebra-hom-Algebra-Monoid :
    hom-Monoid M N ≃
    hom-Algebra-Monoid (algebra-monoid-Monoid M) (algebra-monoid-Monoid N)
  equiv-hom-algebra-hom-Algebra-Monoid =
    ( hom-algebra-monoid-hom-Monoid ,
      is-equiv-hom-algebra-monoid-hom-Monoid)
```
