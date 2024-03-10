# Flat discrete crisp types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-discrete-crisp-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-dependent-functions
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import modal-type-theory.crisp-function-types
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

A crisp type is said to be
{{$concept "flat discrete" Disambiguation="crisp type" Agda=is-flat-discrete-crisp}}
if it is [flat](modal-type-theory.flat-modality.md) modal. I.e. if the flat
counit is an [equivalence](foundation-core.equivalences.md) at that type.

**Terminology:** In _Brouwer's fixed-point theorem in real-cohesive homotopy
type theory_, this is called a _crisply discrete_ type.

## Definition

### Flat discrete crisp types

```agda
module _
  {@♭ l : Level} (@♭ A : UU l)
  where

  is-flat-discrete-crisp : UU l
  is-flat-discrete-crisp = is-equiv (counit-flat {l} {A})

  is-property-is-flat-discrete-crisp : is-prop is-flat-discrete-crisp
  is-property-is-flat-discrete-crisp =
    is-property-is-equiv (counit-flat {l} {A})

  is-flat-discrete-crisp-Prop : Prop l
  is-flat-discrete-crisp-Prop = is-equiv-Prop (counit-flat {l} {A})
```

### Flat discrete crisp families

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  is-flat-discrete-crisp-family : (@♭ B : @♭ A → UU l2) → UU (l1 ⊔ l2)
  is-flat-discrete-crisp-family B = (@♭ x : A) → is-flat-discrete-crisp (B x)
```

### The universal property of flat discrete crisp types

```agda
coev-flat :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ B : UU l2) → ♭ (A → ♭ B) → ♭ (A → B)
coev-flat {A = A} B (cons-flat f) = cons-flat (postcomp A counit-flat f)

universal-property-flat-discrete-crisp-type :
  {@♭ l1 : Level} (@♭ A : UU l1) → UUω
universal-property-flat-discrete-crisp-type A =
  {@♭ l : Level} {@♭ B : UU l} → is-equiv (coev-flat {A = A} B)
```

### The dependent universal property of flat discrete crisp types

```agda
dependent-coev-flat :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ B : A → UU l2) →
  ♭ ((@♭ x : A) → ♭ (B x)) → ♭ ((@♭ x : A) → B x)
dependent-coev-flat B (cons-flat f) = cons-flat (λ x → counit-flat (f x))

dependent-universal-property-flat-discrete-crisp-type :
  {@♭ l1 : Level} (@♭ A : UU l1) → UUω
dependent-universal-property-flat-discrete-crisp-type A =
  {@♭ l : Level} {@♭ B : A → UU l} → is-equiv (dependent-coev-flat B)
```

## Properties

### Flat discrete crisp types satisfy the universal property of flat discrete crisp types

This is Corollary 6.15 of _Brouwer's fixed-point theorem in real-cohesive
homotopy type theory_.

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  abstract
    universal-property-flat-discrete-crisp-type-is-flat-discrete-crisp :
      @♭ is-flat-discrete-crisp A →
      universal-property-flat-discrete-crisp-type A
    universal-property-flat-discrete-crisp-type-is-flat-discrete-crisp
      is-disc-A {B = B} =
      is-equiv-htpy-equiv
        ( ( ap-equiv-flat
            ( equiv-precomp (inv-equiv (counit-flat , is-disc-A)) B)) ∘e
          ( equiv-ap-map-flat-postcomp-counit-flat) ∘e
          ( ap-equiv-flat (equiv-precomp (counit-flat , is-disc-A) (♭ B))))
        ( λ where
          (cons-flat f) →
            crisp-ap
              ( cons-flat)
              ( eq-htpy
                ( λ x →
                  ap
                    ( counit-flat ∘ f)
                    ( inv (is-section-map-inv-is-equiv is-disc-A x)))))
```

### Types `♭ A` are flat discrete

This is Theorem 6.18 of {{#cite Shu17}}.

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-flat-discrete-crisp-flat : is-flat-discrete-crisp (♭ A)
  is-flat-discrete-crisp-flat =
    is-equiv-is-invertible
      ( diagonal-flat)
      ( is-section-diagonal-flat)
      ( is-retraction-diagonal-flat)
```

### The identity types of `♭ A` are flat discrete

```agda
module _
  {@♭ l : Level} {@♭ A : UU l} {@♭ x y : ♭ A}
  where

  is-flat-discrete-crisp-flat-Id-flat :
    is-flat-discrete-crisp (x ＝ y)
  is-flat-discrete-crisp-flat-Id-flat = {!   !}

module _
  {@♭ l : Level} {@♭ A : UU l} {@♭ x y : A}
  where

  is-flat-discrete-crisp-flat-Id :
    is-flat-discrete-crisp (x ＝ y)
  is-flat-discrete-crisp-flat-Id = {!   !}
```

### The empty type is flat discrete

```agda
map-is-flat-discrete-crisp-empty : empty → ♭ empty
map-is-flat-discrete-crisp-empty ()

is-section-map-is-flat-discrete-crisp-empty :
  is-section counit-flat map-is-flat-discrete-crisp-empty
is-section-map-is-flat-discrete-crisp-empty ()

is-retraction-map-is-flat-discrete-crisp-empty :
  is-retraction counit-flat map-is-flat-discrete-crisp-empty
is-retraction-map-is-flat-discrete-crisp-empty (cons-flat ())

abstract
  is-flat-discrete-crisp-empty : is-flat-discrete-crisp empty
  is-flat-discrete-crisp-empty =
    is-equiv-is-invertible
      ( map-is-flat-discrete-crisp-empty)
      ( is-section-map-is-flat-discrete-crisp-empty)
      ( is-retraction-map-is-flat-discrete-crisp-empty)
```

### The unit type is flat discrete

```agda
map-is-flat-discrete-crisp-unit : unit → ♭ unit
map-is-flat-discrete-crisp-unit star = cons-flat star

is-section-map-is-flat-discrete-crisp-unit :
  is-section counit-flat map-is-flat-discrete-crisp-unit
is-section-map-is-flat-discrete-crisp-unit _ = refl

is-retraction-map-is-flat-discrete-crisp-unit :
  is-retraction counit-flat map-is-flat-discrete-crisp-unit
is-retraction-map-is-flat-discrete-crisp-unit (cons-flat _) = refl

abstract
  is-flat-discrete-crisp-unit : is-flat-discrete-crisp unit
  is-flat-discrete-crisp-unit =
    is-equiv-is-invertible
      ( map-is-flat-discrete-crisp-unit)
      ( is-section-map-is-flat-discrete-crisp-unit)
      ( is-retraction-map-is-flat-discrete-crisp-unit)
```

### The type of booleans is flat discrete

```agda
map-is-flat-discrete-crisp-bool : bool → ♭ bool
map-is-flat-discrete-crisp-bool true = cons-flat true
map-is-flat-discrete-crisp-bool false = cons-flat false

is-section-map-is-flat-discrete-crisp-bool :
  is-section counit-flat map-is-flat-discrete-crisp-bool
is-section-map-is-flat-discrete-crisp-bool true = refl
is-section-map-is-flat-discrete-crisp-bool false = refl

is-retraction-map-is-flat-discrete-crisp-bool :
  is-retraction counit-flat map-is-flat-discrete-crisp-bool
is-retraction-map-is-flat-discrete-crisp-bool (cons-flat true) = refl
is-retraction-map-is-flat-discrete-crisp-bool (cons-flat false) = refl

abstract
  is-flat-discrete-crisp-bool : is-flat-discrete-crisp bool
  is-flat-discrete-crisp-bool =
    is-equiv-is-invertible
      ( map-is-flat-discrete-crisp-bool)
      ( is-section-map-is-flat-discrete-crisp-bool)
      ( is-retraction-map-is-flat-discrete-crisp-bool)
```

### The type of natural numbers is flat discrete

```agda
map-is-flat-discrete-crisp-ℕ : ℕ → ♭ ℕ
map-is-flat-discrete-crisp-ℕ zero-ℕ = cons-flat zero-ℕ
map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ap-map-flat succ-ℕ (map-is-flat-discrete-crisp-ℕ x)

compute-map-is-flat-discrete-crisp-ℕ :
  (@♭ x : ℕ) → map-is-flat-discrete-crisp-ℕ x ＝ cons-flat x
compute-map-is-flat-discrete-crisp-ℕ zero-ℕ =
  refl
compute-map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ap (ap-map-flat succ-ℕ) (compute-map-is-flat-discrete-crisp-ℕ x)

is-section-map-is-flat-discrete-crisp-ℕ :
  is-section counit-flat map-is-flat-discrete-crisp-ℕ
is-section-map-is-flat-discrete-crisp-ℕ zero-ℕ =
  refl
is-section-map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ( naturality-counit-flat succ-ℕ (map-is-flat-discrete-crisp-ℕ x)) ∙
  ( ap succ-ℕ (is-section-map-is-flat-discrete-crisp-ℕ x))

is-retraction-map-is-flat-discrete-crisp-ℕ :
  is-retraction counit-flat map-is-flat-discrete-crisp-ℕ
is-retraction-map-is-flat-discrete-crisp-ℕ (cons-flat x) =
  compute-map-is-flat-discrete-crisp-ℕ x

abstract
  is-flat-discrete-crisp-ℕ : is-flat-discrete-crisp ℕ
  is-flat-discrete-crisp-ℕ =
    is-equiv-is-invertible
      ( map-is-flat-discrete-crisp-ℕ)
      ( is-section-map-is-flat-discrete-crisp-ℕ)
      ( is-retraction-map-is-flat-discrete-crisp-ℕ)
```

## See also

- [Sharp codiscrete types](modal-type-theory.sharp-codiscrete-types.md) for the
  dual notion.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
