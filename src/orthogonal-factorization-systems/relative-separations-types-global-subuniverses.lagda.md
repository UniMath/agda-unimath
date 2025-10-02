# Relative separations of types at global subuniverses

```agda
module orthogonal-factorization-systems.relative-separations-types-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.global-subuniverses
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.postcomposition-extensions-maps
```

</details>

## Idea

Consider a [global subuniverse](foundation.global-subuniverses.md) `K` and a map
`δ : X → Y`. A type `A` is said to be
{{#concept "`K`-separated relative to `δ`" Agda=is-rel-separated}} if the type
of extensions of any map `f : X → A` along `δ` is in `K`.

As a special case, a type `A` is _`K`-separated_ if it is `K`-separated relative
to the terminal projection at a two-element type.

## Definitions

### The predicate of being separated

```agda
module _
  {α : Level → Level} {l1 l2 l3 : Level} (K : global-subuniverse α)
  {X : UU l1} {Y : UU l2} (δ : X → Y)
  where

  is-rel-separated : (A : UU l3) → UU (α (l1 ⊔ l2 ⊔ l3) ⊔ l1 ⊔ l3)
  is-rel-separated A =
    (f : X → A) → is-in-global-subuniverse K (extension δ f)

  is-prop-is-rel-separated :
    (A : UU l3) → is-prop (is-rel-separated A)
  is-prop-is-rel-separated A =
    is-prop-Π (λ f → is-prop-is-in-global-subuniverse K (extension δ f))

  is-rel-separated-Prop :
    (A : UU l3) → Prop (α (l1 ⊔ l2 ⊔ l3) ⊔ l1 ⊔ l3)
  is-rel-separated-Prop A =
    ( is-rel-separated A , is-prop-is-rel-separated A)
```

### The global subuniverse of `K`-separated types relative to `δ`

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (K : global-subuniverse α)
  {X : UU l1} {Y : UU l2} (δ : X → Y)
  where

  is-closed-under-equiv-rel-separated-global-subuniverse :
    {l4 l5 : Level} →
    is-closed-under-equiv-subuniverses
      ( λ l3 → α (l1 ⊔ l2 ⊔ l3) ⊔ l1 ⊔ l3)
      ( λ l3 → is-rel-separated-Prop {l3 = l3} K δ)
      ( l4)
      ( l5)
  is-closed-under-equiv-rel-separated-global-subuniverse A B e H f =
    is-closed-under-equiv-global-subuniverse K
      ( extension δ (map-inv-equiv e ∘ f))
      ( extension δ f)
      ( inv-equiv (equiv-postcomp-extension δ f (inv-equiv e)))
      ( H (map-inv-equiv e ∘ f))

  rel-separated-global-subuniverse :
    global-subuniverse (λ l3 → α (l1 ⊔ l2 ⊔ l3) ⊔ l1 ⊔ l3)
  rel-separated-global-subuniverse =
    λ where
    .subuniverse-global-subuniverse l3 →
      is-rel-separated-Prop K δ
    .is-closed-under-equiv-global-subuniverse →
      is-closed-under-equiv-rel-separated-global-subuniverse
```
