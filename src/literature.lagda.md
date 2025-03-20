# Formalization of results from the literature

> This page is currently under construction. To see what's happening behind the
> scenes, see the associated GitHub issue
> [#1055](https://github.com/UniMath/agda-unimath/issues/1055).

## Modules in the literature namespace

```agda
open import foundation.function-extensionality-axiom

module
  literature
  (funext : function-extensionality)
  where

open import literature.100-theorems funext public
open import literature.1000plus-theorems funext public
open import literature.idempotents-in-intensional-type-theory funext public
open import literature.introduction-to-homotopy-type-theory funext public
open import literature.oeis funext public
open import literature.sequential-colimits-in-homotopy-type-theory funext public
```

## References

{{#bibliography}} {{#reference SvDR20}} {{#reference Shu17}}
{{#reference 100theorems}} {{#reference oeis}} {{#reference Rij22}}
