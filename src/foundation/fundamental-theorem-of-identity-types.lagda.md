# The fundamental theorem of identity types

```agda
module foundation.fundamental-theorem-of-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The _fundamental theorem of identity types_ provides a way to characterize
[identity types](foundation-core.identity-types.md). It uses the fact that a
family of maps `f : (x : A) → a ＝ x → B x` is a family of
[equivalences](foundation-core.equivalences.md) if and only if it induces an
equivalence `Σ A (Id a) → Σ A B` on
[total spaces](foundation.dependent-pair-types.md). Note that the total space
`Σ A (Id a)` is [contractible](foundation-core.contractible-types.md).
Therefore, any map `Σ A (Id a) → Σ A B` is an equivalence if and only if `Σ A B`
is contractible. Type families `B` of which the total space `Σ A B` is
contractible are also called
[torsorial](foundation-core.torsorial-type-families.md). The statement of the
fundamental theorem of identity types is therefore:

**Fundamental theorem of identity types.** Consider a type family `B` over a
type `A`, and consider an element `a : A`. Then the following are
[logically equivalent](foundation.logical-equivalences.md):

1. Any family of maps `f : (x : A) → a ＝ x → B x` is a family of equivalences.
2. The type family `B` is torsorial.

## Theorem

### The fundamental theorem of identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a : A}
  where

  abstract
    fundamental-theorem-id :
      is-torsorial B → (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id is-torsorial-B f =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot f) (is-torsorial-Id a) is-torsorial-B)

  abstract
    fundamental-theorem-id' :
      (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f → is-torsorial B
    fundamental-theorem-id' f is-fiberwise-equiv-f =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot f)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
        ( is-torsorial-Id a)
```

## Corollaries

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  abstract
    fundamental-theorem-id-J :
      is-torsorial B → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
    fundamental-theorem-id-J is-torsorial-B =
      fundamental-theorem-id is-torsorial-B (ind-Id a (λ x p → B x) b)

  abstract
    fundamental-theorem-id-J' :
      is-fiberwise-equiv (ind-Id a (λ x p → B x) b) → is-torsorial B
    fundamental-theorem-id-J' H =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot (ind-Id a (λ x p → B x) b))
        ( is-equiv-tot-is-fiberwise-equiv H)
        ( is-torsorial-Id a)
```

### Retracts of the identity type are equivalent to the identity type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  abstract
    fundamental-theorem-id-retraction :
      (i : (x : A) → B x → a ＝ x) →
      ((x : A) → retraction (i x)) →
      is-fiberwise-equiv i
    fundamental-theorem-id-retraction i R =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot i)
          ( is-contr-retract-of
            ( Σ _ (λ y → a ＝ y))
            ( ( tot i) ,
              ( tot (λ x → pr1 (R x))) ,
              ( ( inv-htpy (preserves-comp-tot i (pr1 ∘ R))) ∙h
                ( tot-htpy (pr2 ∘ R)) ∙h
                ( tot-id B)))
            ( is-torsorial-Id a))
          ( is-torsorial-Id a))

    fundamental-theorem-id-retract :
      (R : (x : A) → (B x) retract-of (a ＝ x)) →
      is-fiberwise-equiv (inclusion-retract ∘ R)
    fundamental-theorem-id-retract R =
      fundamental-theorem-id-retraction
        ( inclusion-retract ∘ R)
        ( retraction-retract ∘ R)
```

### The fundamental theorem of identity types, using sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  abstract
    fundamental-theorem-id-section :
      (f : (x : A) → a ＝ x → B x) →
      ((x : A) → section (f x)) →
      is-fiberwise-equiv f
    fundamental-theorem-id-section f section-f x =
      is-equiv-is-equiv-section
        ( f x)
        ( section-f x)
        ( fundamental-theorem-id-retraction
          ( a)
          ( λ x → map-section (f x) (section-f x))
          ( λ x → (f x , is-section-map-section (f x) (section-f x)))
          ( x))
```

## See also

- An extension of the fundamental theorem of identity types is formalized in
  [`foundation.regensburg-extension-fundamental-theorem-of-identity-types`](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).
