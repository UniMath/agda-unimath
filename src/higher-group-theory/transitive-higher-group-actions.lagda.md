# Transitive higher group actions

```agda
module higher-group-theory.transitive-higher-group-actions where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider an [∞-group](higher-group-theory.higher-groups.md) `G` and an
[∞-group action](higher-group-theory.higher-group-actions.md) of `G` on `X`. We
say that `X` is **transitive** if its type of
[orbits](higher-group-theory.orbits-higher-group-actions.md) is
[connected](foundation.connected-types.md).

[Equivalently](foundation.logical-equivalences.md), we say that `X` is
**abstractly transitive** if for any element `x : X (sh G)` of the underlying
type of `X` the action map

```text
  g ↦ mul-action-∞-Group G X g x
```

is [surjective](foundation.surjective-maps.md). The equivalence of these two
conditions is established via the
[Regensburg extension of the fundamental theorem of identity types](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).
