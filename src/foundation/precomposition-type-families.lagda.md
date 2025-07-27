# Precomposition of type families

```agda
module foundation.precomposition-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopy-induction
open import foundation.transport-along-homotopies
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Any map `f : A → B` induces a
{{#concept "precomposition operation" Disambiguation="type families" Agda=precomp-family}}

```text
  (B → 𝒰) → (A → 𝒰)
```

given by [precomposing](foundation-core.precomposition-functions.md) any
`Q : B → 𝒰` to `Q ∘ f : A → 𝒰`.

## Definitions

### The precomposition operation on type families

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  precomp-family : {l : Level} → (B → UU l) → (A → UU l)
  precomp-family Q = Q ∘ f
```

## Properties

### Transport along homotopies in precomposed type families

[Transporting](foundation.transport-along-homotopies.md) along a
[homotopy](foundation.homotopies.md) `H : g ~ h` in the family `Q ∘ f` gives us
a map of families of elements

```text
  ((a : A) → Q (f (g a))) → ((a : A) → Q (f (h a))) .
```

We show that this map is homotopic to transporting along
`f ·l H : f ∘ g ~ f ∘ h` in the family `Q`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  {X : UU l4} {g : X → A}
  where

  statement-tr-htpy-precomp-family :
    {h : X → A} (H : g ~ h) → UU (l3 ⊔ l4)
  statement-tr-htpy-precomp-family H =
    tr-htpy (λ _ → precomp-family f Q) H ~ tr-htpy (λ _ → Q) (f ·l H)

  abstract
    tr-htpy-precomp-family :
      {h : X → A} (H : g ~ h) →
      statement-tr-htpy-precomp-family H
    tr-htpy-precomp-family =
      ind-htpy g
        ( λ h → statement-tr-htpy-precomp-family)
        ( refl-htpy)

    compute-tr-htpy-precomp-family :
      tr-htpy-precomp-family refl-htpy ＝
      refl-htpy
    compute-tr-htpy-precomp-family =
      compute-ind-htpy g
        ( λ h → statement-tr-htpy-precomp-family)
        ( refl-htpy)
```
