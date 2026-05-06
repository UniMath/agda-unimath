# Subtractive semirings

```agda
module ring-theory.subtractive-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.semirings
open import ring-theory.subtractive-ideals-semirings
```

</details>

## Idea

We say that a [semiring](ring-theory.semirings.md) `R` is {{#concept "subtractive" Disambiguation="semiring" Agda=is-subtractive-Semiring}} if every ideal of `R` is [subtractive](ring-theory.subtractive-ideals-semirings.md) {{#cite Nasehpour2016Content}}.

## Definitions

### The predicate of being a subtractive semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-subtractive-Semiring-Level :
    (l : Level) → UU (l1 ⊔ lsuc l)
  is-subtractive-Semiring-Level l =
    (I : ideal-Semiring l R) → is-subtractive-ideal-Semiring R I

  is-subtractive-Semiring : UUω
  is-subtractive-Semiring =
    {l : Level} → is-subtractive-Semiring-Level l
```

## References

{{#bibliography}}
