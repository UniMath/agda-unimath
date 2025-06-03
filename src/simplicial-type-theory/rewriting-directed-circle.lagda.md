# Rewriting rules for the directed circle

```agda
{-# OPTIONS --rewriting #-}

open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.rewriting-directed-circle
  {l1 l2 : Level} (I : Nontrivial-Bounded-Total-Order l1 l2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import reflection.rewriting

open import simplicial-type-theory.directed-circle I
```

</details>

## Idea

This module endows the
[directed circle](simplicial-type-theory.directed-circle.md) with strict
computation rules using Agda's [rewriting](reflection.rewriting.md)
functionality. This gives the strict equality

```text
  ind-directed-circle α (arrow-directed-circle t) ≐
  arrow-free-dependent-directed-loop free-loop-directed-circle α.
```

In addition, the pre-existing witness of this equality
`compute-arrow-ind-directed-circle` reduces to `refl`. This is achieved using
Agda's [equality erasure](reflection.erasing-equality.md) functionality.

To enable this computation rule in your own formalizations, set the
`--rewriting` option and import this module. Keep in mind, however, that we
offer no way to selectively disable these rules, so if your module depends on
any other module that depends on this one, you will necessarily also have
rewriting for the directed circle enabled.

By default, we abstain from using rewrite rules in agda-unimath. However, we
recognize their usefulness in, for instance, exploratory formalizations. Since
formalizations with and without rewrite rules can coexist, there is no harm in
providing these tools for those that see a need to use them. We do, however,
emphasize that formalizations without the use of rewrite rules are preferred
over those that do use them in the library, as the former can also be applied in
other formalizations that do not enable rewrite rules.

## Rewrite rules

```agda
{-# REWRITE compute-arrow-ind-directed-circle #-}
```

## See also

- For some discussion on strict computation rules for higher inductive types,
  see the introduction to Section 6.2 of {{#cite UF13}}.

## References

{{#bibliography}}
