# Naming conventions

A good naming convention is essential for being able to navigate and maintain
the library, and for being able to make progress with your formalization
project. Good names provide concise descriptions of an entry's purpose, and help
making the code in the library readable. On this page we provide general
guidelines for naming entries that apply anywhere in the library.

Accurately naming entries in a large formalization project can be very
difficult, especially when your formalization enters uncharted, or little
written about territory. Giving good names to your entries requires a high level
of conceptual understanding of your entries. The naming scheme should help
reveal common patterns in names, which hopefully helps to find predictable
namings for entries. On the other hand, we understand that this is not always
possible. If you find yourself not knowing what to name something, give it your
best shot to come up with a name, or reach out to us on the
[Univalent Agda discord server](https://discord.gg/Zp2e8hYsuX) to ask if we have
any suggestions. One of the most commonly asked questions is what to name a
certain entry.

We also mention that the naming scheme of agda-unimath evolves as the library
grows. This implies that there are necessarily some inconsistencies in the
naming of our entries, even though we continually work to improve them.
Sometimes we find that old namings don't fit our ideas of a good naming scheme
anymore, or sometimes we gain a better understanding of what an entry is about
and update its name accordingly. We should therefore remember that neither the
naming scheme nor the names we use in the library are set in stone. If you find
a particular entry where the naming seems off, for any reason, we would love to
know about it. Maintaining and improving it is part of the work of maintaining
the agda-unimath library.

## Examples

Before we present a general scheme, let us first get a feel for the structure of names in agda-unimath by considering some examples.
The library has an entry named `is-iso-hom-Ring` for the predicate
that a ring homomorphism is an isomorphsim. The most significant aspect of this
predicate is the assertion that something is an isomorphism. Furthermore, we
make this assertion about ring homomorphisms. The name `is-iso-hom-Ring` is
therefore a logical name for the predicate that a ring homomorphism is an
isomorphism.

In our naming scheme we strive for a direct correspondence between a
construction's name and its type. Take, for example, the proof that the
successor function on integers is an equivalence. It has the type
`is-equiv succ-ℤ`, so we name it `is-equiv-succ-ℤ`.

We also consider the type of hypotheses when naming a construction. Typically,
when including hypotheses in the name, we mention them after the type of the
main construction. Let's take the entry `is-equiv-is-contr-map` as an example.
In this entry, we show that any
[contractible map](foundation.contractible-maps.md) is an
[equivalence](foundation-core.equivalences.md). The type of this entry is therefore
`is-contr-map f → is-equiv f`, where `f` is an assumed function. In the term
`is-equiv-is-contr-map H`, the descriptor `is-contr-map` is positioned adjacent
to its corresponding variable, `H`. Furthermore, by beginning the name with the
descriptor `is-equiv` we quickly see that this entry outputs proofs of
equivalence.

By aligning names with types and incorporating hypotheses when relevant, the
naming scheme aims for clarity and predictability.

## The general scheme

In general, our naming scheme follows the pattern:

```text
  [descriptor]-[output-type]-[input-types]-[Namespace]
```

In this general pattern, all the components are optional. However, their order
is fixed and should be maintained for consistency.

The general naming pattern breaks down as follows:

- **[descriptor]:** This part is used to give a custom descriptive name for the
  entry.
- **[output-type]:** This part of the name refers to the output type of the
  entry.
- **[input-types]:** This part of the name consists of references to the input
  types used in the type specification of the entry.
- **[Namespace]:** This part of the name describes what important concept or
  general category the entry is about.

Given Agda's current lack of a namespace mechanism, we can't have named logical
collections of definitions that span multiple files. Instead, we've incorporated
what would typically be a namespace directly into the name. This convention is
particularly applied to key mathematical concepts, such as groups, rings,
categories, graphs, trees, and so on.

### Naming mathematical structures

We saw, for example, that the prediate `is-iso-hom-Ring` has the part `Ring`
capitalized. This signifies that the predicate is about rings. This name follows
the scheme `[descriptor]-[input-types]-[Namespace]`. Note that there is also the
entry `is-iso-prop-hom-Ring`. This is a predicate that returns for each ring
homomorphism the _proposition_ that it is an isomorphism, and therefore it
follows the scheme `[descriptor]-[output-type]-[input-types]-[Namespace]`. Now
we can guess what a construction named `hom-iso-Ring` should be about: It should
be a construction that constructs the underlying homomorphism of an isomorphisms
of rings. This name follows the pattern
`[output-type]-[input-types]-[Namespace]`.

There is also a common class of entries where we don't use the `[descriptor]`
part in the name of an entry: underlying objects. For example, the underlying
set of a group is called `set-Group`, which uses the pattern
`[output-type]-[Namespace]`. The construction of the underlying set of a group
returns for each group a set, which is an element of type `Set`. Similarly, we
have `type-Group`, `semigroup-Group`, `type-Ring`, `set-Ring`, and so on.
Another instance where this happens is in `hom-iso-Group`, which is the
construction that returns the underlying group homomorphism of an isomorphism of
group. The fact that a group isomorphism is an isomorphsim is called
`is-iso-iso-Group`, which also uses the pattern `[output-type]-[Namespace]`. One
could also consider calling it `is-iso-hom-iso-Group`, to emphasize that the
underlying group homomorphism of the isomorphism is an isomorphism. However,
this name does not fit our patterns in any way, and the addition of `hom` to the
name adds no extra useful information. This situation is common in instances
where we omit the `[descriptor]` part of a name. For instance
`is-category-Category` and `is-ideal-ideal-Ring` follow the patterns
`[output-type]-[Namespace]` and `[output-type]-[input-types]-[Namespace]`,
respectively.

Another class of entries where the naming scheme needs some explanation, is
where we define a structured object from another structured object. For
instance, the [kernel](group-theory.kernels.md) of a
[group homomorphism](group-theory.homomorphisms-groups.md) is defined to be the
[normal subgroup](group-theory.normal-subgroups.md) `kernel-hom-Group`. This
name follows the scheme `[descriptor]-[input-types]-[Namespace]`. When we want
to define the underlying structure of the kernel of a group homomorphism, we
follow the scheme `[output-type]-[input-types]-[Namespace]`. For instance, the
underlying group of the kernel of a group homomorphism is called
`group-kernel-hom-Group`.

### Naming conventions for mathematical laws

Often, mathematical laws are recorded by first specifying in full generality
what it means to satisfy that law. For example, the
[unit laws](foundation.unital-binary-operations.md) for a binary operation are
stated as `left-unit-law` and `right-unit-law`. The fact that
[multiplication on the integers](elementary-number-theory.multiplication-integers.md)
satisfies the unit laws is then stated as `left-unit-law-mul-ℤ` and
`right-unit-law-mul-ℤ`. In the general naming scheme, this naming follows the
pattern `[output-type]-[Namespace]`, because it states the type of which an
element is constructed, and we treat `ℤ` as a namespace.

For a second example, `interchange-law` states what it means to satisfy the
[interchange law](foundation.interchange-law.md). This interchange law requires
two operations. When we want to prove an interchange law for two specific
operations `mul1` and `mul2`, we name it `interchange-law-mul1-mul2`. We use
this naming scheme, even if the two operations are the same. In fact two
_associative_ operations that satisfy the interchange law will necessarily be
the same. For example, in the [integers](elementary-number-theory.integers.md)
there is an interchange law for addition over addition, which states that
`(a + b) + (c + d) ＝ (a + c) + (b + d)`. This law is called
`interchange-law-add-add-ℤ`. Again, this naming follows the pattern
`[output-type]-[Namespace]`, because it states the type of which an element is
constructed.

### Further naming conventions for operations on types

It is also common that we have to record computation laws for functions. For
instance,
[transport along identifications](foundation.transport-along-identifications.md)
in a family of [loop spaces](synthetic-homotopy-theory.loop-spaces.md) acts by
[conjugation](synthetic-homotopy-theory.conjugation-loops.md). The name for
transport along identifications is `tr` and the name for loop spaces in the
library is `Ω`. Therefore, we record the function that transport computes to as
`tr-Ω` and we record the [homotopy](foundation.homotopies.md) that transport is
pointwise equal to `tr-Ω` as `compute-tr-Ω`.

## Overview of our naming conventions

- Names are unique; we steer clear of namespace overloading.

- Names should accurately convey the concept of its construction.

- We use US English spelling of words in names.

- When an entry is predominantly about objects of an important concept, the
  names of these concepts can be capitalized. Usually, these are categories like
  `Prop`, `Set`, `Semigroup`, `Monoid`, `Group`, `Preorder`, `Poset`,
  `Precategory`, `Category`, `Directed-Graph`, `Undirected-Graph`, and so on.

- As a general rule of thumb, names should start out with an all lowercase
  portion with words separated by hyphens, and may have a capitalized portion at
  the end that describes which larger mathematical framework the definition
  takes place in -- for instance, if it is constructed internally to a certain
  subuniverse or category of mathematical objects.

- The start of a name describes the object that is being constructed. For some
  theorems, the latter part of a name describes the hypotheses.

- We use Unicode symbols sparingly and only when they align with established
  mathematical practice.

- Just as we do with abbreviations, we use special symbols sparingly in names.

- If a symbol is not available, we describe the concept concisely in words.

- We prioritize the readability of the code and avoid subtly different
  variations of the same symbol. An important exception is the use of the
  [full width equals sign](https://codepoints.net/U+ff1d) for the identity type,
  as the standard equals sign is a reserved symbol in Agda.

## Naming practices we try to avoid

- Abbreviations might seem like a good way to shorten names, but we use them
  sparingly. They might save a couple of keystrokes for the author, but in the
  grand scheme of things, they will likely compromise readability and
  maintainability, especially for newcomers and maintainers. We aim for clarity,
  not brevity.

- Using Unicode characters in names is permissible, but we recommend restraint
  to maintain readability. Just a few well-placed symbols can often express a
  lot. Often, when we introduce mixfix operators, we also introduce full names
  for them. We then use the full names for these operators in the naming scheme,
  and omit the symbolic notation for anything but the operation itself. For
  example, the commutativity of cartesian products is called `commutative-prod`
  and not `commutative-×`, and the unit of a modality is called `unit-modality`
  and not `unit-○`.

- To improve conceptual clarity, we suggest names of constructions avoid
  referring to variable names. This makes code more understandable, even at a
  glance, and easier to work with in subsequent code.

- Names never reference variables. For example, `G`-sets are called
  [group actions](group-theory.group-actions.md) in our library. The type of all
  group actions on a given group `G` is called `Abstract-Group-Action`. This
  name also contains the prefix `Abstract` in order to disambiguate from
  [concrete group actions](group-theory.concrete-group-actions.md).
