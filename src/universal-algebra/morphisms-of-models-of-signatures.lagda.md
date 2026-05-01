# Morphisms of models of signatures

```agda
module universal-algebra.morphisms-of-models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions

open import lists.finite-sequences
open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of models over a single-sorted finitary algebraic signature" Agda=hom-Model-Of-Signature}}
of `σ`-[models](universal-algebra.models-of-signatures.md) `A` and `B` over a
[single-sorted finitary algebraic signature](universal-algebra.signatures.md)
`σ` is a function `f : A → B` between their underlying
[sets](foundation-core.sets.md) that preserves the operations of `σ`, in the
sense that for `op ∈ σ` an abstract operation with arity `n : ℕ`, and `assign-A`
and `assign-B` the semantics of `σ` in `A` and `B` respectively, and for a
`v : tuple A n`, we have

```text
  f (assign-A op v) = assign-B op (f v).
```

## Definitions

### The predicate on maps of models of preserving operations

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X'@((X , is-set-X) , assign-X) : Model-Of-Signature l2 σ)
  (Y'@((Y , is-set-Y) , assign-Y) : Model-Of-Signature l3 σ)
  (f : type-Model-Of-Signature σ X' → type-Model-Of-Signature σ Y')
  where

  preserves-operations-Model-Of-Signature :
    UU (l1 ⊔ l2 ⊔ l3)
  preserves-operations-Model-Of-Signature =
    ( op : operation-signature σ)
    ( v : tuple X (arity-operation-signature σ op)) →
    f (assign-X op v) ＝ assign-Y op (map-tuple f v)

  abstract
    is-prop-preserves-operations-Model-Of-Signature :
      is-prop preserves-operations-Model-Of-Signature
    is-prop-preserves-operations-Model-Of-Signature =
      is-prop-Π
        ( λ op →
          is-prop-Π
            ( λ v →
              is-set-Y
                ( f (assign-X op v))
                ( assign-Y op (map-tuple f v))))

  prop-preserves-operations-Model-Of-Signature : Prop (l1 ⊔ l2 ⊔ l3)
  prop-preserves-operations-Model-Of-Signature =
    ( preserves-operations-Model-Of-Signature ,
      is-prop-preserves-operations-Model-Of-Signature)
```

### The type of morphisms of models of a signature

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X : Model-Of-Signature l2 σ) (Y : Model-Of-Signature l3 σ)
  where

  hom-Model-Of-Signature : UU (l1 ⊔ l2 ⊔ l3)
  hom-Model-Of-Signature =
    Σ ( type-Model-Of-Signature σ X → type-Model-Of-Signature σ Y)
      ( preserves-operations-Model-Of-Signature σ X Y)

  map-hom-Model-Of-Signature :
    hom-Model-Of-Signature →
    type-Model-Of-Signature σ X → type-Model-Of-Signature σ Y
  map-hom-Model-Of-Signature (f , _) = f

  preserves-operations-hom-Model-Of-Signature :
    (f : hom-Model-Of-Signature) →
    preserves-operations-Model-Of-Signature σ X Y (map-hom-Model-Of-Signature f)
  preserves-operations-hom-Model-Of-Signature (f , p) = p
```

## Properties

### The identity morphism of a model

```agda
module _
  {l1 l2 : Level} (σ : signature l1)
  (X'@((X , _) , assign-X) : Model-Of-Signature l2 σ)
  where

  preserves-operations-id-Model-Of-Signature :
    preserves-operations-Model-Of-Signature σ X' X' id
  preserves-operations-id-Model-Of-Signature op v =
    ap
      ( assign-X op)
      ( preserves-id-map-tuple (arity-operation-signature σ op) v)

  id-hom-Model-Of-Signature : hom-Model-Of-Signature σ X' X'
  id-hom-Model-Of-Signature = (id , preserves-operations-id-Model-Of-Signature)
```

### Characterizing the identity type of morphisms of models

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X : Model-Of-Signature l2 σ) (Y : Model-Of-Signature l3 σ)
  where

  htpy-hom-Model-Of-Signature :
    (f g : hom-Model-Of-Signature σ X Y) → UU (l2 ⊔ l3)
  htpy-hom-Model-Of-Signature (f , _) (g , _) =
    ( x : type-Model-Of-Signature σ X) → f x ＝ g x

  htpy-eq-hom-Model-Of-Signature :
    (f g : hom-Model-Of-Signature σ X Y) →
    f ＝ g → htpy-hom-Model-Of-Signature f g
  htpy-eq-hom-Model-Of-Signature f .f refl = refl-htpy

  abstract
    is-equiv-htpy-eq-hom-Model-Of-Signature :
      (f g : hom-Model-Of-Signature σ X Y) →
      is-equiv (htpy-eq-hom-Model-Of-Signature f g)
    is-equiv-htpy-eq-hom-Model-Of-Signature (f , hom-f) =
      subtype-identity-principle
        ( is-prop-preserves-operations-Model-Of-Signature σ X Y)
        ( hom-f)
        ( refl-htpy)
        ( htpy-eq-hom-Model-Of-Signature (f , hom-f))
        ( funext f)

  extensionality-hom-Model-Of-Signature :
    (f g : hom-Model-Of-Signature σ X Y) →
    (f ＝ g) ≃ htpy-hom-Model-Of-Signature f g
  extensionality-hom-Model-Of-Signature f g =
    ( htpy-eq-hom-Model-Of-Signature f g ,
      is-equiv-htpy-eq-hom-Model-Of-Signature f g)

  eq-htpy-hom-Model-Of-Signature :
    (f g : hom-Model-Of-Signature σ X Y) →
    htpy-hom-Model-Of-Signature f g → f ＝ g
  eq-htpy-hom-Model-Of-Signature f g =
    map-inv-equiv (extensionality-hom-Model-Of-Signature f g)
```

### Homomorphisms of models of signatures preserve the evaluation of terms

```agda
module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (A : Model-Of-Signature l2 σ)
  (B : Model-Of-Signature l3 σ)
  (φ : hom-Model-Of-Signature σ A B)
  where

  abstract
    eval-term-hom-Model-Of-Signature :
      {k : ℕ} →
      (t : term σ k) (v : fin-sequence (type-Model-Of-Signature σ A) k) →
      map-hom-Model-Of-Signature σ A B φ
        ( eval-term-Model-Of-Signature σ A t v) ＝
      eval-term-Model-Of-Signature σ B t
        ( map-hom-Model-Of-Signature σ A B φ ∘ v)

    eval-tuple-term-hom-Model-Of-Signature :
      {k n : ℕ}
      (t : tuple (term σ k) n)
      (v : fin-sequence (type-Model-Of-Signature σ A) k) →
      Eq-tuple
        ( n)
        ( map-tuple
          ( map-hom-Model-Of-Signature σ A B φ)
          ( eval-tuple-term-Model-Of-Signature σ A t v))
        ( eval-tuple-term-Model-Of-Signature σ B t
          ( map-hom-Model-Of-Signature σ A B φ ∘ v))

    eval-term-hom-Model-Of-Signature (var-term i) v = refl
    eval-term-hom-Model-Of-Signature (op-term op ts) v =
      ( preserves-operations-hom-Model-Of-Signature σ A B φ op _) ∙
      ( ap
        ( is-model-set-Model-Of-Signature σ B op)
        ( eq-Eq-tuple _ _ _ (eval-tuple-term-hom-Model-Of-Signature ts v)))

    eval-tuple-term-hom-Model-Of-Signature empty-tuple v = map-raise star
    eval-tuple-term-hom-Model-Of-Signature (t ∷ ts) v =
      ( eval-term-hom-Model-Of-Signature t v ,
        eval-tuple-term-hom-Model-Of-Signature ts v)
```
