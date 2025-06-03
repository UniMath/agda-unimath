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
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.unit-type
open import foundation.universe-levels

open import modal-type-theory.action-on-homotopies-flat-modality
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

A [crisp type](modal-type-theory.crisp-types.md) is said to be
{{#concept "flat discrete" Disambiguation="crisp type" Agda=is-flat-discrete-crisp}}
if it is [flat](modal-type-theory.flat-modality.md) modal. I.e. if the flat
counit is an [equivalence](foundation-core.equivalences.md) at that type.

**Terminology.** In {{#cite Shu18}} this is called a _crisply discrete type_. We
add "flat" as a descriptor to disambiguate from other possible notions of
"discrete types", such as
[types with decidable equality `foundation.discrete-types`](foundation.discrete-types.md).
Moreover, we prefer "discrete crisp type" over "crisply discrete type", as the
former suggests that we assume that the type is crisp, and not that the proof
that it is discrete itself is crisp.

## Definitions

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

### Flat discrete crisp type families

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  is-flat-discrete-crisp-family : (@♭ B : @♭ A → UU l2) → UU (l1 ⊔ l2)
  is-flat-discrete-crisp-family B = (@♭ x : A) → is-flat-discrete-crisp (B x)
```

## Properties

### If the flat counit has a crisp section then it is an equivalence

This is Lemma 6.17 in {{#cite Shu18}}.

```agda
module _
  {@♭ l : Level} {@♭ A : UU l} (@♭ s : A → ♭ A) (@♭ H : counit-flat ∘ s ~ id)
  where

  htpy-retraction-counit-flat-has-crisp-section : s ∘ counit-flat ~ id
  htpy-retraction-counit-flat-has-crisp-section (intro-flat x) =
    inv (is-crisp-retraction-intro-flat (s x)) ∙
    action-flat-htpy H (intro-flat x)

  retraction-counit-flat-has-crisp-section : retraction (counit-flat {A = A})
  retraction-counit-flat-has-crisp-section =
    ( s , htpy-retraction-counit-flat-has-crisp-section)

  is-flat-discrete-crisp-has-crisp-section : is-flat-discrete-crisp A
  is-flat-discrete-crisp-has-crisp-section =
    ( (s , H) , retraction-counit-flat-has-crisp-section)

is-flat-discrete-crisp-crisp-section :
  {@♭ l : Level} {@♭ A : UU l} →
  @♭ section (counit-flat {A = A}) → is-flat-discrete-crisp A
is-flat-discrete-crisp-crisp-section (s , H) =
  is-flat-discrete-crisp-has-crisp-section s H
```

### Flat discrete crisp types are closed under equivalences

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  is-flat-discrete-crisp-equiv :
    @♭ A ≃ B → is-flat-discrete-crisp A → is-flat-discrete-crisp B
  is-flat-discrete-crisp-equiv e bA =
    is-equiv-htpy-equiv'
      ( e ∘e (counit-flat , bA) ∘e action-flat-equiv (inv-equiv e))
      ( λ where (intro-flat x) → is-section-map-inv-equiv e x)

  is-flat-discrete-crisp-equiv' :
    @♭ A ≃ B → is-flat-discrete-crisp B → is-flat-discrete-crisp A
  is-flat-discrete-crisp-equiv' e bB =
    is-equiv-htpy-equiv'
      ( inv-equiv e ∘e (counit-flat , bB) ∘e action-flat-equiv e)
      ( λ where (intro-flat x) → is-retraction-map-inv-equiv e x)
```

### Types in the image of `♭` are flat discrete

This is Theorem 6.18 of {{#cite Shu18}}.

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-flat-discrete-crisp-flat : is-flat-discrete-crisp (♭ A)
  is-flat-discrete-crisp-flat = is-equiv-flat-counit-flat
```

### The crisp identity types of flat discrete crisp types are flat discrete

Given crisp elements `x` and `y` of `A` We have a
[commuting triangle](foundation-core.commuting-triangles-of-maps.md)

```text
                              ♭ (x = y)
                                 ∧   |
                     Eq-eq-flat /~   |
                               /     |
  (intro-flat x = intro-flat y)      | counit-flat
                               \     |
               ap (counit-flat) \    |
                                 ∨   ∨
                                (x = y)
```

where the top-left map `Eq-eq-flat` is an equivalence. Thus, the right map is an
equivalence and `x ＝ y` is a flat discrete crisp type for all crisp `x` and `y`
if and only if the flat counit of `A` is an
[embedding](foundation-core.embeddings.md) on crisp elements. In particular, if
`A` is a flat discrete crisp type then its crisp identity types are too.

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  ( is-crisp-emb-counit-flat-A :
    (@♭ x y : A) → is-equiv (ap (counit-flat) {intro-flat x} {intro-flat y}))
  {@♭ x y : A}
  where

  is-flat-discrete-crisp-Id' : is-flat-discrete-crisp (x ＝ y)
  is-flat-discrete-crisp-Id' =
    is-equiv-right-map-triangle
      ( ap counit-flat {intro-flat x} {intro-flat y})
      ( counit-flat)
      ( Eq-eq-flat (intro-flat x) (intro-flat y))
      ( λ where refl → refl)
      ( is-crisp-emb-counit-flat-A x y)
      ( is-equiv-Eq-eq-flat (intro-flat x) (intro-flat y))

module _
  {@♭ l : Level} {@♭ A : UU l}
  (is-emb-counit-flat-A : is-emb (counit-flat {A = A}))
  {@♭ x y : A}
  where

  is-flat-discrete-crisp-Id : is-flat-discrete-crisp (x ＝ y)
  is-flat-discrete-crisp-Id =
    is-flat-discrete-crisp-Id'
      ( λ x y → is-emb-counit-flat-A (intro-flat x) (intro-flat y))

module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-flat-discrete-crisp-flat-Id :
    {@♭ u v : ♭ A} → is-flat-discrete-crisp (u ＝ v)
  is-flat-discrete-crisp-flat-Id {intro-flat x} {intro-flat y} =
    is-flat-discrete-crisp-Id (is-emb-is-equiv is-flat-discrete-crisp-flat)
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
is-retraction-map-is-flat-discrete-crisp-empty (intro-flat ())

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
map-is-flat-discrete-crisp-unit star = intro-flat star

is-section-map-is-flat-discrete-crisp-unit :
  is-section counit-flat map-is-flat-discrete-crisp-unit
is-section-map-is-flat-discrete-crisp-unit _ = refl

is-retraction-map-is-flat-discrete-crisp-unit :
  is-retraction counit-flat map-is-flat-discrete-crisp-unit
is-retraction-map-is-flat-discrete-crisp-unit (intro-flat _) = refl

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
map-is-flat-discrete-crisp-bool true = intro-flat true
map-is-flat-discrete-crisp-bool false = intro-flat false

is-section-map-is-flat-discrete-crisp-bool :
  is-section counit-flat map-is-flat-discrete-crisp-bool
is-section-map-is-flat-discrete-crisp-bool true = refl
is-section-map-is-flat-discrete-crisp-bool false = refl

is-retraction-map-is-flat-discrete-crisp-bool :
  is-retraction counit-flat map-is-flat-discrete-crisp-bool
is-retraction-map-is-flat-discrete-crisp-bool (intro-flat true) = refl
is-retraction-map-is-flat-discrete-crisp-bool (intro-flat false) = refl

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
map-is-flat-discrete-crisp-ℕ zero-ℕ = intro-flat zero-ℕ
map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  action-flat-map succ-ℕ (map-is-flat-discrete-crisp-ℕ x)

compute-map-is-flat-discrete-crisp-ℕ :
  (@♭ x : ℕ) → map-is-flat-discrete-crisp-ℕ x ＝ intro-flat x
compute-map-is-flat-discrete-crisp-ℕ zero-ℕ =
  refl
compute-map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ap (action-flat-map succ-ℕ) (compute-map-is-flat-discrete-crisp-ℕ x)

is-section-map-is-flat-discrete-crisp-ℕ :
  is-section counit-flat map-is-flat-discrete-crisp-ℕ
is-section-map-is-flat-discrete-crisp-ℕ zero-ℕ =
  refl
is-section-map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ( naturality-counit-flat succ-ℕ (map-is-flat-discrete-crisp-ℕ x)) ∙
  ( ap succ-ℕ (is-section-map-is-flat-discrete-crisp-ℕ x))

is-retraction-map-is-flat-discrete-crisp-ℕ :
  is-retraction counit-flat map-is-flat-discrete-crisp-ℕ
is-retraction-map-is-flat-discrete-crisp-ℕ (intro-flat x) =
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
- [The universal property of flat discrete crisp types](modal-type-theory.universal-property-flat-discrete-crisp-types.md)
- [The dependent universal property of flat discrete crisp types](modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.md)

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
