# Rewriting

```agda
{-# OPTIONS --rewriting #-}

module reflection.rewriting where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.identity-types
```

</details>

## Idea

Agda's rewriting functionality allows us to add new strict equalities to our
type theory. Given an equality `β : x ＝ y`, then adding a rewrite rule for `β`
with

```text
{-# REWRITE β #-}
```

will make it so `x` rewrites to `y`, i.e., `x ≐ y`.

**Warning.** Rewriting is by nature a very unsafe tool so we advice exercising
abundant caution when defining such rules.

## Definitions

We declare to Agda that the [identity relation](foundation.identity-types.md)
may be used to define rewrite rules.

```agda
{-# BUILTIN REWRITE _＝_ #-}
```

## See also

- [Erasing equality](reflection.erasing-equality.md)

## External links

- [Rewriting](https://agda.readthedocs.io/en/latest/language/rewriting.html) at
  Agda's documentation pages
