# Naming conventions

A good naming convention is essential for being able to navigate and maintain
the library, and for being able to make progress with your formalization
project. Good names provide coincise descriptions of an entry's purpose, and
help making the code in the library readable. On this page we provide general
guidelines for naming entries that apply anywhere in the library.

We also mention that the naming scheme of agda-unimath evolves as agda grows.
Sometimes we find that old namings don't fit our ideas of a good naming scheme
anymore, or we find other ways to improve on the naming. Some older code in the
library might even not be updated yet to fit the current naming scheme. We
should therefore remember that the naming scheme is not set in stone, and
maintaining and improving it is part of the work of maintaining the agda-unimath
library.

Finally, we should note that accurately naming entries in a large formalization
project can be very difficult, especially when your formalization enters
unchartered, or little written about territory. Giving good names to your
entries requires a high level of conceptual understanding of your entries. The
naming scheme should help reveal common patterns in names, which hopefully helps
to find predictable namings for entries. On the other hand, we understand that
this is not always possible. If you find yourself not knowing what to name
something, give it your best shot to come up with a name, or reach out to us on
the Univalent Agda discord to ask if we have any suggestions.

## Examples

The library contains, for example, an entry `is-iso-hom-Ring` for the predicate
that a ring homomorphism is an isomorphsim. The most significant aspect of this
predicate is the assertion that something is an isomorphism. Furthermore, we
make this assertion about ring homomorphisms. The name `is-iso-hom-Ring` is
therefore a logical name for the predicate that a ring homomorphism is an
isomorphism.

In our naming scheme we strive for a direct correspondence between a
construction's name and its type. Take, for example, the proof that the
successor function on integers is an equivalence. It has the type
`is-equiv succ-ℤ`, so we name it `is-equiv-succ-ℤ`.

We may also reflect the type of hypotheses used in the construction within the
name. If we wish to do so, we name the hypotheses after we have named the type
of the construction. For instance, `is-equiv-is-contr-map` is a function of type
`is-contr-map f → is-equiv f`, where `f` is a given function. Notice how the
term `is-equiv-is-contr-map H` places the descriptor `is-contr-map` right next
to the variable `H` it refers to. Another advantage is that the name says
immediately what it constructs.

## The general scheme

In general, our naming scheme follows the following pattern:

```text
  [name]-[type]-[hypotheses]-[Namespace]
```

We note that Agda has, as of yet, no namespace mechanism. This means that in
places where we wished to be able to use namespaces, we would append the name of
an entry with the name that we would have given to that namespace. We use this
naming convention for important mathematical concepts, such as groups, rings,
categories, graphs, trees, and so on. Furthermore, we note that in the general
naming scheme above all parts are optional, but the order of the different parts
of the name must be respected.

### Naming mathematical structures

We saw, for example, that the prediate `is-iso-hom-Ring` has the part `Ring`
capitalized. This signifies that the predicate is about rings. This name follows
the scheme `[name]-[hypotheses]-[Namespace]`. Note that there is also the entry
`is-iso-prop-hom-Ring`. This is a predicate that returns for each ring
homomorphism the _proposition_ that it is an isomorphism, and therefore it
follows the scheme `[name]-[type]-[hypotheses]-[Namespace]`. Now we can guess
what a construction named `hom-iso-Ring` should be about: It should be a
construction that constructs the underlying homomorphism of an isomorphisms of
rings. This name follows the pattern `[type]-[hypotheses]-[Namespace]`.

There is also a common class of entries where we don't use the `[name]` part in
the name of an entry: underlying objects. For example, the underlying set of a
group is called `set-Group`, which uses the pattern `[type]-[Namespace]`. The
construction of the underlying set of a group returns for each group a set,
which is an element of type `Set`. Similarly, we have `type-Group]`,
`semigroup-Group`, `type-Ring`, `set-Ring`, and so on. Another instance where
this happens is in `hom-iso-Group`, which is the construction that returns the
underlying group homomorphism of an isomorphism of group. The fact that a group
isomorphism is an isomorphsim is called `is-iso-iso-Group`, which also uses the
pattern `[type]-[Namespace]`. One could also consider calling it
`is-iso-hom-iso-Group`, to emphasize that the underlying group homomorphism of
the isomorphism is an isomorphism. However, this name does not fit our patterns
in any way, and the addition of `hom` to the name adds no extra useful
information. This situation is common in instances where we omit the `[name]`
part of a name. For instance `[is-category-Category` and `is-ideal-ideal-Ring`
follow the patterns `[type]-[Namespace]` and `[type]-[hypotheses]-[Namespace]`.

Another class of entries where the naming scheme needs some explanation, is
where we define a structured object from another structured object. For
instance, the [kernel](group-theory.kernels.md) of a
[group homomorphism](group-theory.homomorphisms-groups.md) is defined to be the
[normal subgroup](group-theory.normal-subgroups.md) `kernel-hom-Group`. This
name follows the scheme
`[name]-[hypotheses]-[Namespace]`. When we want to define the underlying structure of the kernel of a group homomorphism, we follow the scheme `[type]-[hypotheses]-[Namespace]`. For instance, the underlying group of the kernel of a group homomorphism is called `group-kernel-hom-Group`.

### Naming conventions for mathematical laws

Often, mathematical laws are recorded by first specifying in full generality
what it means to satisfy that law. For example, the
[unit laws](foundation.unital-binary-operations.md) for a binary operation are
stated as `left-unit-law` and `right-unit-law`. The fact that
[multiplication on the integers](elementary-number-theory.multiplication-integers.md)
satisfies the unit laws is then stated as `left-unit-law-mul-ℤ` and
`right-unit-law-mul-ℤ`. In the general naming scheme, this naming follows the
pattern `[type]-[Namespace]`, because it states the type of which an element is
constructed, and we treat `ℤ` as a namespace.

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
`[type]-[Namespace]`, because it states the type of which an element is
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

## Abbreviations, and avoiding them

We should also mention that, while abbreviations might seem like a good way to
shorten names, we use them sparingly. They might save a couple of keystrokes for
the author, but in the grand scheme of things, they will likely compromise
readability and maintainability, especially for newcomers and maintainers. We
aim for clarity, not brevity.

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

If you are unsure about what to name your entry, ask us on the Univalent Agda
discord server. One of the most commonly asked questions is what to name a
certain thing.

## Naming conventions we try to avoid

- Using Unicode characters in names is entirely permissible, but we recommend
  restraint to maintain readability. Just a few well-placed symbols can often
  express a lot.

- To enhance conceptual clarity, we suggest names of constructions avoid
  referring to variable names. This makes code more understandable, even at a
  glance, and easier to work with in subsequent code.

- Using the projection functions `pr1` and `pr2`, particularly their
  compositions, can lead to short code, but we recommend to avoid doing so. When
  constructions contain a lot of projections throughout their definition, the
  projections reveal little of what is going on in that part of the projections.
  We therefore prefer naming the projections. When a type of the form `Σ A B` is
  given a name, naming its projections too can enhance readability and will
  provide more informative responses when jumping to the definition.
  Furthermore, it makes it easier to change the definition later on.

- Lastly, we recommend not naming constructions after infix notation of
  operations included in them. Preferring primary prefix notation over infix
  notation can help keep our code consistent. For example, it's preferred to use
  `commutative-prod` instead of `commutative-×` for denoting the commutativity
  of cartesian products.

- Names never reference variables.
