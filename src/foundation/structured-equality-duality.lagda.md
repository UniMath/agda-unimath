# Structured equality duality

```agda
module foundation.structured-equality-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.maps-in-subuniverses
open import foundation.separated-types-subuniverses
open import foundation.structure
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.equivalences
```

</details>

## Idea

Given a [structure](foundation.structure.md) `𝒫` on types that transfers along
[equivalences](foundation-core.equivalences.md) in the sense that `𝒫` comes
equipped with a family of maps

```text
  {X Y : 𝒰} → (X ≃ Y) → 𝒫 X → 𝒫 Y,
```

then for every type `A` and type family `B : A → 𝒰` there is a
[mutual correspondence](foundation.logical-equivalences.md) between the
following:

1. `𝒫`-structured families of maps `f : (y : A) → (x ＝ y) → B y` for every
   `x : A`.
2. `𝒫`-structures on the equality of `Σ A B`.

We refer to this as
{{#concept "structured equality duality" Agda=structured-equality-duality}}.

**Note.** by [the univalence axiom](foundation.univalence.md), every structure
[transfers along equivalences](foundation.transport-along-equivalences.md).
However, we maintain this as an assumption, since for most common notions of
structure this property is independent of the univalence axiom.

One potential but crude justification for using the term "duality" for this
principle is as follows. The principle gives a correspondence between structures
on families of _maps mapping into_ the **type family** `B`, and structures on
the binary family of equality over the _dependent sum_ `Σ A B`, and so, in a
certain sense, one is trading one straightened dimension for another.

## Duality

### Structured equality duality

```agda
module _
  {l1 l2 l3 : Level} {𝒫 : UU (l1 ⊔ l2) → UU l3}
  (tr-𝒫 : {X Y : UU (l1 ⊔ l2)} → X ≃ Y → 𝒫 X → 𝒫 Y)
  {A : UU l1} {B : A → UU l2}
  where

  forward-implication-structured-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y)) →
    structure-equality 𝒫 (Σ A B)
  forward-implication-structured-equality-duality
    K (x , b) (x' , b') =
    tr-𝒫
      ( compute-fiber-map-out-of-identity-type (ind-Id x (λ u _ → B u) b) x' b')
      ( K x (ind-Id x (λ u _ → B u) b) x' b')

  backward-implication-structured-equality-duality :
    structure-equality 𝒫 (Σ A B) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y))
  backward-implication-structured-equality-duality K x f y b =
    tr-𝒫
      ( inv-compute-fiber-map-out-of-identity-type f y b)
      ( K (x , f x refl) (y , b))

  structured-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y)) ↔
    ( structure-equality 𝒫 (Σ A B))
  structured-equality-duality =
    ( forward-implication-structured-equality-duality ,
      backward-implication-structured-equality-duality)
```

### Subuniverse equality duality

Given a [subuniverse](foundation.subuniverses.md) `𝒫` then the following are
logically equivalent:

1. For every `x : A`, every family of maps `f : (y : A) → (x ＝ y) → B y` is a
   family of `𝒫`-maps.
2. The dependent sum `Σ A B` is `𝒫`-separated.

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse (l1 ⊔ l2) l3)
  (tr-𝒫 :
    {X Y : UU (l1 ⊔ l2)} →
    X ≃ Y → is-in-subuniverse 𝒫 X → is-in-subuniverse 𝒫 Y)
  {A : UU l1} {B : A → UU l2}
  where

  forward-implication-subuniverse-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y)) →
    is-separated 𝒫 (Σ A B)
  forward-implication-subuniverse-equality-duality =
    forward-implication-structured-equality-duality tr-𝒫

  backward-implication-subuniverse-equality-duality :
    is-separated 𝒫 (Σ A B) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y))
  backward-implication-subuniverse-equality-duality =
    backward-implication-structured-equality-duality tr-𝒫

  subuniverse-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y)) ↔
    is-separated 𝒫 (Σ A B)
  subuniverse-equality-duality =
    structured-equality-duality tr-𝒫
```

## See also

This duality is applied in

- [The Regensburg extension of the fundamental theorem of identity types](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md)
- [The strong preunivalence axiom](foundation.strong-preunivalence.md)
- [Strongly preunivalent categories](category-theory.strongly-preunivalent-categories.md)
