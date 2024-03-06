# Whiskering homotopies with respect to concatenation

```agda
module foundation.whiskering-homotopies-concatenation where

open import foundation-core.whiskering-homotopies-concatenation public
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation
open import foundation.whiskering-operations

open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
```

</details>

## Idea

Consider a homotopy `H : f ~ g` and a homotopy `K : I ~ J` between two
homotopies `I J : g ~ f`. The
{{#concept "left whiskering" Disambiguation="homotopies with respect to concatenation" Agda=left-whisker-concat-htpy}}
of `H` and `K` is a homotopy `H ∙h I ~ H ∙h J`. In other words, left whiskering
of homotopies with respect to concatenation is a
[whiskering operation](foundation.whiskering-operations.md)

```text
  (H : f ~ g) {I J : g ~ h} → I ~ J → H ∙h I ~ H ∙h K.
```

Similarly, we introduce
{{#concept "right whiskering" Disambiguation="homotopies with respect to concatenation" Agda=right-whisker-concat-htpy}}
to be an operation

```text
  {H I : f ~ g} → H ~ I → (J : g ~ h) → H ∙h J ~ I ∙h J.
```

## Properties

### Left whiskering of homotopies with respect to concatenation is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equiv-left-whisker-concat-htpy :
    {f g h : (x : A) → B x} (H : f ~ g) {I J : g ~ h} →
    is-equiv (left-whisker-concat-htpy H {I} {J})
  is-equiv-left-whisker-concat-htpy H =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ x → is-equiv-left-whisker-concat (H x))
```

### Right whiskering of homotopies with respect to concatenation is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equiv-right-whisker-concat-htpy :
    {f g h : (x : A) → B x} {H I : f ~ g} (J : g ~ h) →
    is-equiv (λ (K : H ~ I) → right-whisker-concat-htpy K J)
  is-equiv-right-whisker-concat-htpy J =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ x → is-equiv-right-whisker-concat (J x))
```
